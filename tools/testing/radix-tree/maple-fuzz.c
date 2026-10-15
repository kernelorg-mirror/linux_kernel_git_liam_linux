// SPDX-License-Identifier: GPL-2.0+
/*
 * maple-fuzz.c: VMA-shaped fuzzing of the maple tree API.
 *
 * Built from maple.c with -DMAPLE_FUZZ so the tree internals and the test
 * helpers are in scope.  Builds a tree from a maps file or a generated
 * address space, then runs passes of random mmap/munmap-like operations
 * against a sorted-array model.  Every pass must exercise a split, a
 * spanning store and a rebalance; what the random operations did not reach
 * is forced with a directed store.  The tree is validated after each pass.
 */

#include <errno.h>
#include <getopt.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define MF_RING		64
/* Ops between structure checks: the op that broke the tree is in the ring. */
#define MF_CHECK_EVERY	(MF_RING / 2)
#define MF_PAGE_SHIFT	12
#define MF_NR_STORE	(wr_slot_store + 1)

enum mf_opcode {
	MF_MMAP_UP,
	MF_MMAP_DOWN,
	MF_MMAP_FIXED,
	MF_MUNMAP,
	MF_SPLIT,
	MF_MERGE,
	MF_EXPAND,
	MF_SHRINK,
	MF_MOVE,
	MF_BRK,
	MF_ERASE,
	MF_SIMPLE,
	MF_FORK,
	MF_RESET,
	MF_RCU,
	MF_NONKERNEL,
	MF_LOAD,
	MF_WALK,
	MF_CHAIN,
	MF_RANGES,
	MF_GAP,
	MF_MARK,
	MF_ALLOC,
	MF_DIRECTED,
	MF_NR_OPS,
};

static const char * const mf_op_name[MF_NR_OPS] = {
	"mmap_up", "mmap_down", "mmap_fixed", "munmap", "split", "merge",
	"expand", "shrink", "move", "brk", "erase", "simple", "fork", "reset",
	"rcu", "nonkernel", "load", "walk", "chain", "ranges", "gap", "mark",
	"alloc", "directed",
};

static const unsigned char mf_op_weight[MF_NR_OPS] = {
	7, 9, 7, 9, 6, 5, 5, 5, 4, 3, 2, 2, 1, 1, 1, 2, 4, 4, 4, 5, 4, 6, 4, 0,
};

/* What -a sweeps, each with and without RCU; -L comes from the command line. */
static const struct {
	unsigned int flags;
	bool pfn;
	const char *name;
} mf_config[] = {
	{ MT_FLAGS_ALLOC_RANGE, false, "alloc" },
	{ 0, false, "range" },
	{ MT_FLAGS_MARKS, false, "marks" },
	{ MT_FLAGS_ALLOC_RANGE, true, "alloc dense" },
	{ 0, true, "range dense" },
	{ MT_FLAGS_MARKS, true, "marks dense" },
};

static const char * const mf_store_name[MF_NR_STORE] = {
	"invalid", "new_root", "store_root", "exact_fit", "spanning", "split",
	"rebalance", "append", "node_store", "slot_store",
};

struct mf_vma {
	u32 id;
	u32 flags;
	bool live;
};

struct mf_ival {
	u64 start;
	u64 last;
	struct mf_vma *vma;
	u8 marks;
};

struct mf_op {
	u32 pass;
	u32 seq;
	u8 op;
	u64 a;
	u64 b;
	u64 c;
};

static struct {
	const char *maps;
	const char *save;
	const char *crash;
	u64 gen;
	u64 top_arg;
	u64 top;
	u64 floor_arg;
	u64 floor;
	u64 seed;
	u64 rng;
	u64 unit;
	unsigned int passes;
	unsigned int ops;
	unsigned int below4g;
	unsigned int promote;
	unsigned int flags;
	unsigned int nreaders;
	unsigned int configs;
	bool pfn;
	bool sweep;
	bool verbose;
	bool leak;

	struct maple_tree mt;

	struct mf_ival *v;
	size_t n;
	size_t cap;
	size_t target;		/* ranges after the build, held near */
	size_t nmin, nmax;	/* ranges and height seen over the passes */
	unsigned int hmin, hmax;

	struct mf_vma **vmas;
	size_t nvmas;
	size_t cvmas;
	u32 next_id;

	unsigned int hist[MF_NR_STORE];
	struct mf_op ring[MF_RING];
	char ring_text[MF_RING][128];
	unsigned int ring_pos;
	unsigned int pass;
	unsigned int seq;
	bool failing;
	bool rebuilt;		/* a split, spanning store or rebalance ran */
	unsigned int since;	/* ops since the last structure check */
} mf;

/* PRNG */

static u64 mf_rand_r(u64 *state)
{
	u64 x = *state;

	x ^= x >> 12;
	x ^= x << 25;
	x ^= x >> 27;
	*state = x;
	return x * 0x2545F4914F6CDD1DULL;
}

static u64 mf_rand(void)
{
	return mf_rand_r(&mf.rng);
}

static u64 mf_rand_below(u64 n)
{
	return n ? mf_rand() % n : 0;
}

static bool mf_chance(unsigned int pct)
{
	return mf_rand_below(100) < pct;
}

/*
 * Failure reporting.  The terminal gets the message and the last operations;
 * the whole report, with the model and the tree, goes to the crash file.
 */

static void mf_print_maps(FILE *f);

static void mf_dump_tree(FILE *f)
{
	MA_STATE(mas, &mf.mt, 0, 0);
	void *entry;

	rcu_read_lock();
	entry = mas_walk(&mas);
	for (;;) {
		struct mf_vma *v = entry;

		fprintf(f, "  %llx-%llx %s%u\n",
			(unsigned long long)mas.index,
			(unsigned long long)mas.last,
			v ? "id " : "NULL", v ? v->id : 0);
		if (!mas_is_active(&mas) || mas.last == U64_MAX)
			break;
		entry = mas_next_range(&mas, U64_MAX);
		if (!mas_is_active(&mas))
			break;
	}
	rcu_read_unlock();
}

/* mt_dump() prints to stdout; point that at @f while it runs. */
static void mf_mt_dump(FILE *f)
{
	int saved;

	fflush(stdout);
	saved = dup(STDOUT_FILENO);
	if (saved >= 0)
		dup2(fileno(f), STDOUT_FILENO);
	mt_dump(&mf.mt, mt_dump_hex);
	fflush(stdout);
	if (saved >= 0) {
		dup2(saved, STDOUT_FILENO);
		close(saved);
	}
}

static void mf_write_ring(int fd)
{
	unsigned int i;

	for (i = 0; i < MF_RING; i++) {
		const char *text = mf.ring_text[(mf.ring_pos + i) % MF_RING];

		if (text[0] && write(fd, text, strlen(text)) < 0)
			break;
	}
}

static void mf_report(FILE *f)
{
	unsigned int i;

	fprintf(f, "last operations (oldest first):\n");
	fflush(f);
	mf_write_ring(fileno(f));
	fprintf(f, "store types this pass:");
	for (i = 0; i < MF_NR_STORE; i++)
		fprintf(f, " %s=%u", mf_store_name[i], mf.hist[i]);
	fprintf(f, "\nmodel: %zu ranges\n", mf.n);
	for (i = 0; i < mf.n; i++)
		fprintf(f, "  %llx-%llx id %u marks %02x\n",
			(unsigned long long)mf.v[i].start,
			(unsigned long long)mf.v[i].last, mf.v[i].vma->id,
			mf.v[i].marks);
	fprintf(f, "model (maps syntax):\n");
	mf_print_maps(f);
	fprintf(f, "tree:\n");
	mf_dump_tree(f);
	fflush(f);
	mf_mt_dump(f);
}

/* The crash file, or stderr when it cannot be made. */
static FILE *mf_crash_file(void)
{
	FILE *f = fopen(mf.crash, "w");

	if (!f) {
		fprintf(stderr, "maple-fuzz: %s: %s\n", mf.crash, strerror(errno));
		return stderr;
	}
	return f;
}

static void mf_crash_done(FILE *f)
{
	if (f == stderr)
		return;
	fclose(f);
	fprintf(stderr, "full report in %s\n", mf.crash);
}

/*
 * A crash inside the tree: the model is the tree's content before the
 * failing operation, the dump its shape.
 */
static void mf_death(const char *why)
{
	static const char hdr[] = "maple-fuzz: last operations (oldest first):\n";
	FILE *f;

	if (mf.failing)
		return;
	mf.failing = true;
	if (write(2, hdr, sizeof(hdr) - 1) < 0)
		return;
	mf_write_ring(2);
	f = mf_crash_file();
	fprintf(f, "maple-fuzz: crash seed %llu pass %u op %u: %s; the model is from before the operation\n",
		(unsigned long long)mf.seed, mf.pass, mf.seq, why);
	mf_report(f);
	mf_crash_done(f);
}

static void mf_sigabrt(int sig)
{
	mf_death("abort, the BUG line is in the output before the ring");
	signal(sig, SIG_DFL);
	raise(sig);
}

static void mf_sanitizer_death(void)
{
	mf_death("sanitizer report, in the output before the ring");
}

static void __attribute__((format(printf, 1, 2), noreturn))
mf_fail(const char *fmt, ...)
{
	va_list ap;
	char msg[256];
	FILE *f;

	va_start(ap, fmt);
	vsnprintf(msg, sizeof(msg), fmt, ap);
	va_end(ap);
	fprintf(stderr, "maple-fuzz: FAIL seed %llu pass %u op %u: %s\n",
		(unsigned long long)mf.seed, mf.pass, mf.seq, msg);
	fprintf(stderr, "last operations (oldest first):\n");
	mf_write_ring(2);

	f = mf_crash_file();
	fprintf(f, "maple-fuzz: FAIL seed %llu pass %u op %u: %s\n",
		(unsigned long long)mf.seed, mf.pass, mf.seq, msg);
	mf_report(f);
	mf_crash_done(f);
	mf.failing = true;
	abort();
}

static void mf_record(enum mf_opcode op, u64 a, u64 b, u64 c)
{
	struct mf_op *rec = &mf.ring[mf.ring_pos];

	mf.seq++;
	rec->pass = mf.pass;
	rec->seq = mf.seq;
	rec->op = op;
	rec->a = a;
	rec->b = b;
	rec->c = c;
	snprintf(mf.ring_text[mf.ring_pos], sizeof(mf.ring_text[0]),
		 "  %u/%u %s %llx %llx %llx\n", rec->pass, rec->seq,
		 mf_op_name[op], (unsigned long long)a, (unsigned long long)b,
		 (unsigned long long)c);
	if (mf.verbose)
		fputs(mf.ring_text[mf.ring_pos], stderr);
	mf.ring_pos = (mf.ring_pos + 1) % MF_RING;
}

/* Entries */

static struct mf_vma *mf_vma_new(void)
{
	struct mf_vma *v = malloc(sizeof(*v));

	if (!v)
		mf_fail("malloc");
	v->id = ++mf.next_id;
	v->flags = mf_rand_below(2);
	v->live = false;
	if (mf.nvmas == mf.cvmas) {
		mf.cvmas = mf.cvmas ? mf.cvmas * 2 : 1024;
		mf.vmas = realloc(mf.vmas, mf.cvmas * sizeof(*mf.vmas));
		if (!mf.vmas)
			mf_fail("realloc");
	}
	mf.vmas[mf.nvmas++] = v;
	return v;
}

/* Free what the model dropped.  Only valid once the tree has matched it. */
static void mf_sweep_vmas(void)
{
	size_t i, kept = 0;

	for (i = 0; i < mf.n; i++)
		mf.v[i].vma->live = true;
	for (i = 0; i < mf.nvmas; i++) {
		struct mf_vma *v = mf.vmas[i];

		if (!v->live) {
			free(v);
			continue;
		}
		v->live = false;
		mf.vmas[kept++] = v;
	}
	mf.nvmas = kept;
}

/* Model: sorted, non-overlapping intervals; gaps are implicit. */

static size_t model_first_after(u64 idx)
{
	size_t lo = 0, hi = mf.n;

	while (lo < hi) {
		size_t mid = lo + (hi - lo) / 2;

		if (mf.v[mid].last < idx)
			lo = mid + 1;
		else
			hi = mid;
	}
	return lo;
}

static struct mf_ival *model_find(u64 idx)
{
	size_t i = model_first_after(idx);

	if (i < mf.n && mf.v[i].start <= idx)
		return &mf.v[i];
	return NULL;
}

static void model_insert(size_t pos, u64 start, u64 last, struct mf_vma *vma,
			 u8 marks)
{
	if (mf.n == mf.cap) {
		mf.cap = mf.cap ? mf.cap * 2 : 1024;
		mf.v = realloc(mf.v, mf.cap * sizeof(*mf.v));
		if (!mf.v)
			mf_fail("realloc");
	}
	memmove(&mf.v[pos + 1], &mf.v[pos], (mf.n - pos) * sizeof(*mf.v));
	mf.v[pos].start = start;
	mf.v[pos].last = last;
	mf.v[pos].vma = vma;
	mf.v[pos].marks = marks;
	mf.n++;
}

/* The first range at or after @idx that starts by @max and has @mark. */
static struct mf_ival *model_marked_after(u64 idx, u64 max, mt_mark_t mark)
{
	size_t i;

	for (i = model_first_after(idx); i < mf.n && mf.v[i].start <= max; i++)
		if (mf.v[i].marks & BIT(mark))
			return &mf.v[i];
	return NULL;
}

/* The last range at or before @idx that ends from @min and has @mark. */
static struct mf_ival *model_marked_before(u64 idx, u64 min, mt_mark_t mark)
{
	size_t i = model_first_after(idx);

	if (i == mf.n || mf.v[i].start > idx) {
		if (!i)
			return NULL;
		i--;
	}
	for (;; i--) {
		if (mf.v[i].last < min)
			return NULL;
		if (mf.v[i].marks & BIT(mark))
			return &mf.v[i];
		if (!i)
			return NULL;
	}
}

static void model_remove(size_t pos, size_t count)
{
	memmove(&mf.v[pos], &mf.v[pos + count],
		(mf.n - pos - count) * sizeof(*mf.v));
	mf.n -= count;
}

/*
 * The same (index, last, entry) that went to the tree.  A value takes the
 * marks of every range it covers; what is left of a cut range keeps its own.
 */
static void model_update(u64 start, u64 last, struct mf_vma *vma)
{
	size_t i = model_first_after(start), j;
	u8 marks = 0;

	for (j = i; vma && j < mf.n && mf.v[j].start <= last; j++)
		marks |= mf.v[j].marks;

	if (i < mf.n && mf.v[i].start < start && mf.v[i].last > last) {
		model_insert(i + 1, last + 1, mf.v[i].last, mf.v[i].vma,
			     mf.v[i].marks);
		mf.v[i].last = start - 1;
		if (vma)
			model_insert(i + 1, start, last, vma, marks);
		return;
	}

	if (i < mf.n && mf.v[i].start < start) {
		mf.v[i].last = start - 1;
		i++;
	}

	j = i;
	while (j < mf.n && mf.v[j].last <= last)
		j++;
	if (j < mf.n && mf.v[j].start <= last)
		mf.v[j].start = last + 1;

	model_remove(i, j - i);
	if (vma)
		model_insert(i, start, last, vma, marks);
}

static bool mf_fits(u64 gs, u64 ge, u64 lo, u64 hi, u64 size, bool lowest,
		    u64 *idx, u64 *last)
{
	if (gs > lo)
		lo = gs;
	if (ge < hi)
		hi = ge;
	if (hi < lo || hi - lo < size - 1)
		return false;

	if (lowest) {
		*idx = lo;
		*last = lo + size - 1;
	} else {
		*last = hi;
		*idx = hi - size + 1;
	}
	return true;
}

/*
 * The lowest or highest free run of @size within [lo, hi], the way
 * mas_empty_area() and mas_empty_area_rev() define it: everything above the
 * last range is free to U64_MAX.
 */
static bool model_gap(u64 lo, u64 hi, u64 size, bool lowest, u64 *idx,
		      u64 *last)
{
	size_t i;

	if (lowest) {
		u64 gs = 0;

		for (i = 0; i < mf.n; i++) {
			if (gs > hi)
				return false;
			if (mf.v[i].start > gs &&
			    mf_fits(gs, mf.v[i].start - 1, lo, hi, size, true,
				    idx, last))
				return true;
			gs = mf.v[i].last + 1;
			if (!gs)
				return false;
		}
		return mf_fits(gs, U64_MAX, lo, hi, size, true, idx, last);
	}

	{
		u64 ge = U64_MAX;

		for (i = mf.n; i-- > 0;) {
			if (ge < lo)
				return false;
			if (mf.v[i].last < ge &&
			    mf_fits(mf.v[i].last + 1, ge, lo, hi, size, false,
				    idx, last))
				return true;
			if (!mf.v[i].start)
				return false;
			ge = mf.v[i].start - 1;
		}
		return mf_fits(0, ge, lo, hi, size, false, idx, last);
	}
}

/* Random values */

static u64 mf_align(u64 x)
{
	return x & ~(mf.unit - 1);
}

static u64 mf_pages(void)
{
	unsigned int r = mf_rand_below(100);

	if (r < 40)
		return 1;
	if (r < 70)
		return 2 + mf_rand_below(15);
	if (r < 95)
		return 17 + mf_rand_below(1008);
	if (r < 99)
		return 1025 + mf_rand_below(15360);
	return 1 + mf_rand_below((mf.top / mf.unit) / 4 + 1);
}

static u64 mf_size(void)
{
	return mf_pages() * mf.unit;
}

static u64 mf_addr(void)
{
	u64 seam = (u64)U32_MAX + 1;
	u64 a;

	if (mf.pfn)
		seam >>= MF_PAGE_SHIFT;

	switch (mf_rand_below(10)) {
	case 0:
		if (mf.n)
			return mf.v[mf_rand_below(mf.n)].start;
		break;
	case 1:
		if (mf.n) {
			a = mf.v[mf_rand_below(mf.n)].last + 1;
			if (a && a <= mf.top)
				return a;
		}
		break;
	case 2:
		if (mf.n) {
			a = mf.v[mf_rand_below(mf.n)].start;
			if (a >= mf.floor + mf.unit)
				return a - mf.unit;
		}
		break;
	case 3:
		if (mf.n) {
			struct mf_ival *iv = &mf.v[mf_rand_below(mf.n)];

			return iv->start +
			       mf_align(mf_rand_below(iv->last - iv->start + 1));
		}
		break;
	case 4:
		return mf.floor;
	case 5:
		if (mf.top >= mf.floor + 64 * mf.unit)
			return mf_align(mf.top - mf_rand_below(64) * mf.unit);
		break;
	case 6:
		if (seam >= mf.floor + 32 * mf.unit &&
		    seam + 64 * mf.unit <= mf.top)
			return seam - 32 * mf.unit + mf_rand_below(64) * mf.unit;
		break;
	}

	return mf.floor + mf_align(mf_rand_below(mf.top - mf.floor + 1));
}

/* A size to cut out: small while the model is below the size it was built with. */
static u64 mf_cut(void)
{
	u64 size = mf_size();

	if (mf.n < mf.target && size > 16 * mf.unit)
		size = (1 + mf_rand_below(16)) * mf.unit;
	return size;
}

/* A random range [start, last] within the space, page aligned. */
static bool mf_range(u64 *start, u64 *last)
{
	u64 size = mf_cut();
	u64 s = mf_addr();

	if (mf.top - mf.floor < size - 1)
		return false;
	if (s > mf.top - size + 1)
		s = mf_align(mf.top - size + 1);
	*start = s;
	*last = s + size - 1;
	return *last >= *start && *last <= mf.top;
}

/* The highest index the tree can report: its ceiling, U64_MAX when empty. */
static u64 mf_ceiling(void)
{
	MA_STATE(mas, &mf.mt, 0, 0);
	u64 ceiling;

	rcu_read_lock();
	mas_walk(&mas);
	ceiling = mas_is_active(&mas) ? mas_tree_max(&mas) : U64_MAX;
	rcu_read_unlock();
	return ceiling;
}

/* An address in the tree, near its ceiling now and then, rarely above it. */
static u64 mf_probe(u64 ceiling)
{
	u64 a = mf_addr();

	if (ceiling < U64_MAX && mf_chance(5))
		return mf_chance(50) ? U64_MAX :
				       ceiling + 1 + mf_rand_below(64) * mf.unit;
	if (a > ceiling)
		a = mf_align(ceiling - mf_rand_below(64) * mf.unit);
	return a;
}

static void mf_expect(const char *what, void *got, void *want)
{
	struct mf_vma *g = got, *w = want;

	if (got != want)
		mf_fail("%s: got %s%u want %s%u", what, g ? "id " : "NULL",
			g ? g->id : 0, w ? "id " : "NULL", w ? w->id : 0);
}

static void mf_expect_range(const char *what, struct ma_state *mas, u64 start,
			    u64 last)
{
	if (mas->index != start || mas->last != last)
		mf_fail("%s: range %llx-%llx want %llx-%llx", what,
			(unsigned long long)mas->index,
			(unsigned long long)mas->last,
			(unsigned long long)start, (unsigned long long)last);
}

/* The gap a NULL walk reports at @idx: the model's, bounded by the tree. */
static void mf_expect_gap(const char *what, struct ma_state *mas, u64 idx)
{
	size_t i = model_first_after(idx);
	u64 gs = i ? mf.v[i - 1].last + 1 : 0;
	u64 gl = (i < mf.n) ? mf.v[i].start - 1 : U64_MAX;

	if (mas_is_active(mas)) {
		if (gl == U64_MAX)
			gl = mas_tree_max(mas);
	} else {
		u64 ceiling = mf_ceiling();

		/* Above the ceiling only the gap from the ceiling up is seen. */
		if (idx > ceiling)
			gs = ceiling + 1;
		gl = ULONG_MAX;
	}
	mf_expect_range(what, mas, gs, gl);
}

/* Right after a store, the slot holding @start is what was stored. */
static void mf_readback(u64 start, u64 last, struct mf_vma *vma)
{
	MA_STATE(mas, &mf.mt, start, start);

	rcu_read_lock();
	mf_expect("readback", mas_walk(&mas), vma);
	if (vma)
		mf_expect_range("readback", &mas, start, last);
	else
		mf_expect_gap("readback", &mas, start);
	rcu_read_unlock();
}

static void model_store(u64 start, u64 last, struct mf_vma *vma)
{
	model_update(start, last, vma);
	mf_readback(start, last, vma);
}

/* Tree helpers mirroring mm/vma.h and include/linux/mm.h */

static void mf_tally(struct ma_state *mas)
{
	if (mas->store_type < MF_NR_STORE)
		mf.hist[mas->store_type]++;
	/* These build new nodes; the tree is validated soon after. */
	if (mas->store_type == wr_split_store ||
	    mas->store_type == wr_spanning_store ||
	    mas->store_type == wr_rebalance)
		mf.rebuilt = true;
}

static void mf_prealloc_store(struct ma_state *mas, struct mf_vma *vma)
{
	int ret = mas_preallocate(mas, vma, GFP_KERNEL);

	if (ret)
		mf_fail("mas_preallocate %d", ret);
	mf_tally(mas);
	mas_store_prealloc(mas, vma);
}

/* vma_iter_store_overwrite(): the state may be anywhere. */
static void vmi_store(struct ma_state *mas, u64 start, u64 last,
		      struct mf_vma *vma)
{
	if (!mas_is_start(mas) && (mas->index > start || mas->last < start))
		mas_pause(mas);
	__mas_set_range(mas, start, last);
	mf_prealloc_store(mas, vma);
	model_store(start, last, vma);
}

/* vma_iter_clear_gfp() */
static void vmi_clear(struct ma_state *mas, u64 start, u64 last)
{
	int ret;

	if (!mas_is_start(mas) && (mas->index > start || mas->last < start))
		mas_pause(mas);
	__mas_set_range(mas, start, last);
	ret = mas_store_gfp(mas, NULL, GFP_KERNEL);
	if (ret)
		mf_fail("mas_store_gfp %d", ret);
	mf_tally(mas);
	model_store(start, last, NULL);
}

/*
 * vms_gather_munmap_vmas(): split the ranges cut by [start, last] so only
 * whole ranges lie inside, and leave @mas at the range holding @start.
 */
static void vmi_gather(struct ma_state *mas, u64 start, u64 last)
{
	void *entry;
	u64 vl;

	mas_set(mas, start);
	entry = mas_find(mas, last);
	if (entry) {
		vl = mas->last;
		if (mas->index < start) {
			vmi_store(mas, start, vl, mf_vma_new());
		}
		for (;;) {
			if (vl > last) {
				vmi_store(mas, last + 1, vl, mf_vma_new());
				break;
			}
			if (vl == last)
				break;
			entry = mas_find(mas, last);
			if (!entry)
				break;
			vl = mas->last;
		}
	}

	while (mas->index > start)
		mas_prev_range(mas, 0);
}

/* Write operations */

static bool mf_mergeable(struct mf_vma *a, struct mf_vma *b)
{
	return (a->flags & 1) == (b->flags & 1);
}

/* unmapped_area() / unmapped_area_topdown() then __mmap_new_vma() */
static void op_mmap(bool down)
{
	u64 size = mf_size(), lo = mf.floor, hi = mf.top, eidx, elast;
	struct mf_ival *prev = NULL, *next = NULL;
	struct mf_vma *vma, *n;
	size_t i;
	bool found;
	int ret;
	MA_STATE(mas, &mf.mt, 0, 0);
	MA_STATE(m2, &mf.mt, 0, 0);

	if (mf_chance(30))
		lo = mf_addr();
	if (mf_chance(30))
		hi = mf_addr() | (mf.unit - 1);
	if (lo > hi || hi - lo < size - 1)
		return;

	mf_record(down ? MF_MMAP_DOWN : MF_MMAP_UP, lo, hi, size);
	mtree_lock(&mf.mt);
	if (down)
		ret = mas_empty_area_rev(&mas, lo, hi, size);
	else
		ret = mas_empty_area(&mas, lo, hi, size);
	found = model_gap(lo, hi, size, !down, &eidx, &elast);
	if (ret != 0 && ret != -EBUSY)
		mf_fail("mas_empty_area %d", ret);
	if ((ret == 0) != found)
		mf_fail("gap search ret %d, model %sfound", ret,
			found ? "" : "not ");
	if (!found) {
		mtree_unlock(&mf.mt);
		return;
	}
	mf_expect_range("gap search", &mas, eidx, elast);

	/* vma_next() then vma_prev() as unmapped_area() does. */
	i = model_first_after(elast == U64_MAX ? elast : elast + 1);
	n = mas_find(&mas, U64_MAX);
	mf_expect("gap next", n, (elast != U64_MAX && i < mf.n) ?
		  mf.v[i].vma : NULL);
	if (n) {
		mf_expect("gap prev", mas_prev(&mas, 0),
			  i ? mf.v[i - 1].vma : NULL);
	}

	/* The store, from a fresh iterator. */
	mas_set(&m2, eidx);
	mf_expect("gap find", mas_find(&m2, elast), NULL);
	vma = mf_vma_new();
	if (eidx) {
		prev = model_find(eidx - 1);
		if (prev && !mf_mergeable(prev->vma, vma))
			prev = NULL;
	}
	if (elast != U64_MAX) {
		next = model_find(elast + 1);
		if (next && !mf_mergeable(next->vma, vma))
			next = NULL;
	}

	if (prev) {
		u64 ps = prev->start, nl = next ? next->last : elast;
		struct mf_vma *pv = prev->vma;

		mf_expect("merge prev", mas_prev(&m2, 0), pv);
		vmi_store(&m2, ps, nl, pv);
	} else if (next) {
		u64 nl = next->last;

		vmi_store(&m2, eidx, nl, next->vma);
	} else {
		vmi_store(&m2, eidx, elast, vma);
	}
	mas_destroy(&m2);
	mtree_unlock(&mf.mt);
}

/* MAP_FIXED: __mmap_setup() gathers, __mmap_new_vma() stores over it. */
static void op_mmap_fixed(void)
{
	u64 start, last;
	bool abort_path = mf_chance(25);
	MA_STATE(mas, &mf.mt, 0, 0);
	MA_STATE(m2, &mf.mt, 0, 0);

	if (!mf_range(&start, &last))
		return;

	mf_record(MF_MMAP_FIXED, start, last, abort_path);
	mtree_lock(&mf.mt);
	vmi_gather(&mas, start, last);
	if (abort_path) {
		vmi_clear(&mas, start, last);
		vmi_store(&m2, start, last, mf_vma_new());
		mas_destroy(&m2);
	} else {
		vmi_store(&mas, start, last, mf_vma_new());
	}
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
}

static void mf_munmap(u64 start, u64 last)
{
	MA_STATE(mas, &mf.mt, 0, 0);

	mtree_lock(&mf.mt);
	vmi_gather(&mas, start, last);
	vmi_clear(&mas, start, last);
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
}

static void op_munmap(void)
{
	u64 start, last;

	if (!mf_range(&start, &last))
		return;
	mf_record(MF_MUNMAP, start, last, 0);
	mf_munmap(start, last);
}

/* A random range of the model with at least @pages pages, or false. */
static bool mf_pick(u64 pages, size_t *pos)
{
	unsigned int tries;

	if (!mf.n)
		return false;
	for (tries = 0; tries < 8; tries++) {
		size_t i = mf_rand_below(mf.n);

		if (mf.v[i].last - mf.v[i].start + 1 >= pages * mf.unit) {
			*pos = i;
			return true;
		}
	}
	return false;
}

/* __split_vma(): the tail becomes a new vma. */
static void op_split(void)
{
	size_t i;
	u64 start, last, cut;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (!mf_pick(2, &i))
		return;
	start = mf.v[i].start;
	last = mf.v[i].last;
	cut = start + mf.unit * (1 + mf_rand_below((last - start + 1) /
						     mf.unit - 1));
	mf_record(MF_SPLIT, start, last, cut);
	mtree_lock(&mf.mt);
	mas_set(&mas, start);
	mf_expect("split walk", mas_walk(&mas), mf.v[i].vma);
	vmi_store(&mas, cut, last, mf_vma_new());
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
}

/* commit_merge(): prev, prev and next, or a cut inside the middle. */
static void op_merge(void)
{
	size_t i = mf_rand_below(mf.n);
	struct mf_ival prev, mid, next;
	bool have_prev, have_next;
	unsigned int variant;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (mf.n < 2)
		return;
	mid = mf.v[i];
	have_prev = i && mf.v[i - 1].last + 1 == mid.start &&
		    mf_mergeable(mf.v[i - 1].vma, mid.vma);
	have_next = i + 1 < mf.n && mid.last + 1 == mf.v[i + 1].start &&
		    mf_mergeable(mf.v[i + 1].vma, mid.vma);
	if (!have_prev && !have_next)
		return;
	if (have_prev)
		prev = mf.v[i - 1];
	if (have_next)
		next = mf.v[i + 1];

	variant = mf_rand_below(4);
	mtree_lock(&mf.mt);
	if (have_prev && have_next && variant == 0) {
		mf_record(MF_MERGE, prev.start, next.last, 0);
		mas_set(&mas, prev.start);
		mf_expect("merge walk", mas_walk(&mas), prev.vma);
		vmi_store(&mas, prev.start, next.last, prev.vma);
	} else if (have_prev && (variant <= 1 ||
				 mid.last - mid.start + 1 < 2 * mf.unit)) {
		mf_record(MF_MERGE, prev.start, mid.last, 1);
		mas_set(&mas, prev.start);
		mf_expect("merge walk", mas_walk(&mas), prev.vma);
		vmi_store(&mas, prev.start, mid.last, prev.vma);
	} else if (have_prev && variant == 2) {
		u64 cut = mid.start + mf.unit *
			  (1 + mf_rand_below((mid.last - mid.start + 1) /
					     mf.unit - 1));

		/* __adjust_middle_start(): prev takes the head of mid. */
		mf_record(MF_MERGE, prev.start, cut - 1, 2);
		mas_set(&mas, prev.start);
		mf_expect("merge walk", mas_walk(&mas), prev.vma);
		vmi_store(&mas, prev.start, cut - 1, prev.vma);
	} else if (have_next) {
		u64 cut = mid.start;

		/* __adjust_next_start(): next takes the tail of mid. */
		if (mid.last - mid.start + 1 >= 2 * mf.unit && mf_chance(50))
			cut = mid.start + mf.unit *
			      (1 + mf_rand_below((mid.last - mid.start + 1) /
						 mf.unit - 1));
		mf_record(MF_MERGE, cut, next.last, 3);
		mas_set(&mas, mid.start);
		mf_expect("merge walk", mas_walk(&mas), mid.vma);
		vmi_store(&mas, cut, next.last, next.vma);
	}
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
}

/* vma_expand() into the gap after, or expand_downwards() into the gap before. */
static void op_expand(void)
{
	size_t i = mf_rand_below(mf.n);
	u64 size = mf_size(), gap, start, last;
	struct mf_vma *vma;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (!mf.n)
		return;
	start = mf.v[i].start;
	last = mf.v[i].last;
	vma = mf.v[i].vma;
	if (mf_chance(50)) {
		gap = (i + 1 < mf.n) ? mf.v[i + 1].start - 1 : mf.top;
		if (gap <= last)
			return;
		if (gap - last < size)
			size = gap - last;
		mf_record(MF_EXPAND, start, last + size, 0);
		mtree_lock(&mf.mt);
		mas_set(&mas, start);
		mf_expect("expand walk", mas_walk(&mas), vma);
		vmi_store(&mas, start, last + size, vma);
	} else {
		gap = i ? mf.v[i - 1].last + 1 : mf.floor;
		if (gap >= start)
			return;
		if (start - gap < size)
			size = start - gap;
		mf_record(MF_EXPAND, start - size, last, 1);
		mtree_lock(&mf.mt);
		mas_set(&mas, start - 1);
		mf_expect("expand walk", mas_walk(&mas), NULL);
		vmi_store(&mas, start - size, last, vma);
	}
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
}

/* vma_shrink(): prealloc then clear, with no range reset in between. */
static void op_shrink(void)
{
	size_t i;
	u64 start, last, cut;
	bool tail = mf_chance(50);
	int ret;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (!mf_pick(2, &i))
		return;
	start = mf.v[i].start;
	last = mf.v[i].last;
	cut = start + mf.unit * (1 + mf_rand_below((last - start + 1) /
						     mf.unit - 1));
	mf_record(MF_SHRINK, start, last, tail ? cut : cut - 1);
	mtree_lock(&mf.mt);
	mas_set(&mas, start);
	mf_expect("shrink walk", mas_walk(&mas), mf.v[i].vma);
	if (tail)
		__mas_set_range(&mas, cut, last);
	else
		__mas_set_range(&mas, start, cut - 1);
	ret = mas_preallocate(&mas, NULL, GFP_KERNEL);
	if (ret)
		mf_fail("mas_preallocate %d", ret);
	mf_tally(&mas);
	mas_store_prealloc(&mas, NULL);
	if (tail)
		model_store(cut, last, NULL);
	else
		model_store(start, cut - 1, NULL);
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
}

/* mremap(MREMAP_MAYMOVE): link the copy first, then unmap the source. */
static void op_move(void)
{
	size_t i = mf_rand_below(mf.n);
	u64 start, last, size, eidx, elast;
	int ret;
	MA_STATE(mas, &mf.mt, 0, 0);
	MA_STATE(m2, &mf.mt, 0, 0);

	if (!mf.n)
		return;
	start = mf.v[i].start;
	last = mf.v[i].last;
	size = last - start + 1;
	mtree_lock(&mf.mt);
	ret = mas_empty_area_rev(&mas, mf.floor, mf.top, size);
	if (ret) {
		mtree_unlock(&mf.mt);
		return;
	}
	if (!model_gap(mf.floor, mf.top, size, false, &eidx, &elast))
		mf_fail("move: tree found a gap the model has not");
	mf_expect_range("move gap", &mas, eidx, elast);
	mf_record(MF_MOVE, start, last, eidx);
	vmi_store(&m2, eidx, elast, mf_vma_new());
	mas_destroy(&m2);
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
	mf_munmap(start, last);
}

/* do_brk_flags(): grow the highest range, or vma_iter_store_gfp() a new one. */
static void op_brk(void)
{
	struct mf_ival top;
	u64 size = mf_size(), last;
	int ret;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (!mf.n)
		return;
	top = mf.v[mf.n - 1];
	if (top.last >= mf.top)
		return;
	if (mf.top - top.last < size)
		size = mf.top - top.last;
	last = top.last + size;
	if (mf_chance(50)) {
		mf_record(MF_BRK, top.start, last, 0);
		mtree_lock(&mf.mt);
		mas_set(&mas, top.start);
		mf_expect("brk walk", mas_walk(&mas), top.vma);
		vmi_store(&mas, top.start, last, top.vma);
	} else {
		struct mf_vma *vma = mf_vma_new();

		mf_record(MF_BRK, top.last + 1, last, 1);
		mtree_lock(&mf.mt);
		__mas_set_range(&mas, top.last + 1, last);
		ret = mas_store_gfp(&mas, vma, GFP_KERNEL);
		if (ret)
			mf_fail("mas_store_gfp %d", ret);
		mf_tally(&mas);
		model_store(top.last + 1, last, vma);
	}
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
}

static void op_erase(void)
{
	size_t i = mf_rand_below(mf.n);
	struct mf_ival iv;
	u64 idx;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (!mf.n)
		return;
	iv = mf.v[i];
	idx = iv.start + mf_align(mf_rand_below(iv.last - iv.start + 1));
	mf_record(MF_ERASE, iv.start, iv.last, idx);
	mtree_lock(&mf.mt);
	mas_set(&mas, idx);
	mf_expect("erase", mas_erase(&mas), iv.vma);
	mf_tally(&mas);
	model_store(iv.start, iv.last, NULL);
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
}

static void op_simple(void)
{
	u64 start, last;
	struct mf_vma *vma = NULL;
	int ret;

	if (!mf_range(&start, &last))
		return;
	if (mf_chance(60))
		vma = mf_vma_new();
	mf_record(MF_SIMPLE, start, last, vma ? vma->id : 0);
	ret = mtree_store_range_u64(&mf.mt, start, last, vma, GFP_KERNEL);
	if (ret)
		mf_fail("mtree_store_range_u64 %d", ret);
	model_store(start, last, vma);
}

/* Set or clear a mark, by state or by the mtree wrappers, then read it back. */
static void op_mark(void)
{
	u64 idx = mf_probe(mf_ceiling());
	struct mf_ival *iv;
	mt_mark_t mark = mf_rand_below(MT_MARK_MAX + 1);
	bool set = mf_chance(60), api = mf_chance(50);
	int ret;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (mf.n && mf_chance(80)) {
		iv = &mf.v[mf_rand_below(mf.n)];
		idx = iv->start + mf_align(mf_rand_below(iv->last - iv->start + 1));
	} else {
		iv = model_find(idx);
	}
	mf_record(MF_MARK, idx, mark, set);

	if (api && set) {
		ret = mtree_set_mark_u64(&mf.mt, idx, mark);
	} else if (api) {
		ret = mtree_clear_mark_u64(&mf.mt, idx, mark);
	} else {
		mtree_lock(&mf.mt);
		mas_set(&mas, idx);
		if (set)
			mas_set_mark(&mas, mark);
		else
			mas_clear_mark(&mas, mark);
		ret = mas_is_err(&mas) ? xa_err(mas.node) : 0;
		mtree_unlock(&mf.mt);
	}
	/* A tree without marks refuses them. */
	if (ret != (mt_has_marks(&mf.mt) ? 0 : -EINVAL))
		mf_fail("mark %u at %llx: returned %d", mark,
			(unsigned long long)idx, ret);

	/* A NULL takes no mark, nor does a tree without them. */
	if (iv && mt_has_marks(&mf.mt)) {
		if (set)
			iv->marks |= BIT(mark);
		else
			iv->marks &= ~BIT(mark);
		idx = iv->start + mf_align(mf_rand_below(iv->last - iv->start + 1));
	}
	if (mtree_get_mark_u64(&mf.mt, idx, mark) !=
	    (iv && (iv->marks & BIT(mark))))
		mf_fail("mark %u at %llx: tree and model disagree", mark,
			(unsigned long long)idx);
}

/* The allocators: IDs over a window with the cyclic one, or a sized fit. */
static void op_alloc(void)
{
	u64 lo = mf_addr(), hi = lo + mf_rand_below(256) * mf.unit;
	u64 idx, want, last;
	bool alloc = mt_is_alloc(&mf.mt), found;
	int ret;

	if (hi > mf.top)
		hi = mf.top;
	if (hi < lo)
		return;

	if (mf.pfn) {
		u64 next = lo + mf_rand_below(hi - lo + 1);
		unsigned int k, n = 1 + mf_rand_below(32);
		bool api = mf_chance(50);
		MA_STATE(mas, &mf.mt, 0, 0);

		mf_record(MF_ALLOC, lo, hi, n);

		for (k = 0; k < n; k++) {
			struct mf_vma *vma = mf_vma_new();
			u64 from = next > lo ? next : lo;
			bool wrap = false;

			found = model_gap(from, hi, 1, true, &want, &last);
			if (!found && from > lo) {
				found = model_gap(lo, hi, 1, true, &want, &last);
				wrap = found;
			}
			if (api) {
				ret = mtree_alloc_cyclic_u64(&mf.mt, &idx, vma, lo,
							     hi, &next, GFP_KERNEL);
			} else {
				mtree_lock(&mf.mt);
				ret = mas_alloc_cyclic(&mas, &idx, vma, lo, hi,
						       &next, GFP_KERNEL);
				mtree_unlock(&mf.mt);
			}
			if (!found) {
				if (ret != -EBUSY)
					mf_fail("cyclic: ret %d with the window full",
						ret);
				break;
			}
			if (ret != wrap || idx != want)
				mf_fail("cyclic: %llx ret %d want %llx ret %d",
					(unsigned long long)idx, ret,
					(unsigned long long)want, wrap);
			model_store(idx, idx, vma);
		}
		return;
	}

	{
		u64 size = mf_size();
		bool rev = mf_chance(50);
		struct mf_vma *vma;

		if (hi - lo < size - 1)
			return;
		vma = mf_vma_new();
		mf_record(MF_ALLOC, lo, hi, size);
		found = model_gap(lo, hi, size, !rev, &want, &last);
		if (rev)
			ret = mtree_alloc_rrange_u64(&mf.mt, &idx, vma, size, lo,
						     hi, GFP_KERNEL);
		else
			ret = mtree_alloc_range_u64(&mf.mt, &idx, vma, size, lo,
						    hi, GFP_KERNEL);
		if (!alloc) {
			if (ret != -EINVAL)
				mf_fail("alloc_range: ret %d on a tree without gaps",
					ret);
			return;
		}
		if (ret != (found ? 0 : -EBUSY))
			mf_fail("alloc_range: ret %d, model %sfound", ret,
				found ? "" : "not ");
		if (!found)
			return;
		if (idx != want)
			mf_fail("alloc_range: %llx want %llx",
				(unsigned long long)idx, (unsigned long long)want);
		model_store(idx, idx + size - 1, vma);
	}
}

/* Validation */

static void mf_check_forward(struct maple_tree *mt)
{
	MA_STATE(mas, mt, 0, 0);
	size_t i = 0;
	u64 pos = 0;
	void *entry;

	rcu_read_lock();
	entry = mas_walk(&mas);
	for (;;) {
		struct mf_vma *want;
		u64 want_last;
		u8 want_marks = 0;

		if (i < mf.n && mf.v[i].start == pos) {
			want = mf.v[i].vma;
			want_last = mf.v[i].last;
			want_marks = mf.v[i].marks;
			i++;
		} else {
			want = NULL;
			want_last = (i < mf.n) ? mf.v[i].start - 1 : U64_MAX;
		}

		mf_expect("forward walk", entry, want);
		if (mas.index != pos)
			mf_fail("forward walk: index %llx want %llx",
				(unsigned long long)mas.index,
				(unsigned long long)pos);
		if (mt_has_marks(mt) && mas_is_active(&mas) &&
		    mas_marks(&mas)[mas.offset] != want_marks)
			mf_fail("forward walk: marks %02x want %02x at %llx",
				mas_marks(&mas)[mas.offset], want_marks,
				(unsigned long long)pos);

		if (!want && want_last == U64_MAX) {
			u64 limit = mas_is_active(&mas) ? mas_tree_max(&mas) :
							  ULONG_MAX;

			if (mas.last != limit)
				mf_fail("forward walk: trailing gap ends %llx want %llx",
					(unsigned long long)mas.last,
					(unsigned long long)limit);
			break;
		}
		if (mas.last != want_last)
			mf_fail("forward walk: last %llx want %llx at %llx",
				(unsigned long long)mas.last,
				(unsigned long long)want_last,
				(unsigned long long)pos);
		if (want_last == U64_MAX)
			break;

		pos = want_last + 1;
		if (mas_is_active(&mas) && pos > mas_tree_max(&mas)) {
			if (i < mf.n)
				mf_fail("forward walk: ranges above the ceiling");
			break;
		}
		entry = mas_next_range(&mas, U64_MAX);
		if (!mas_is_active(&mas)) {
			/* Only the gap after a root pointer ends this way. */
			if (i < mf.n || mas.index != pos ||
			    mas.last != ULONG_MAX)
				mf_fail("forward walk: tree ended at %llx",
					(unsigned long long)pos);
			break;
		}
	}
	rcu_read_unlock();
}

static void mf_check_reverse(struct maple_tree *mt)
{
	MA_STATE(mas, mt, 0, 0);
	size_t i = mf.n;
	u64 top, pos;
	void *entry;

	rcu_read_lock();
	mas_walk(&mas);
	if (!mas_is_active(&mas)) {
		rcu_read_unlock();
		return;
	}
	top = mas_tree_max(&mas);
	while (i && mf.v[i - 1].start > top)
		i--;
	pos = top;
	mas_set(&mas, top);
	entry = mas_walk(&mas);
	for (;;) {
		struct mf_vma *want;
		u64 want_start;

		if (i && mf.v[i - 1].last >= pos) {
			want = mf.v[i - 1].vma;
			want_start = mf.v[i - 1].start;
			i--;
		} else {
			want = NULL;
			want_start = i ? mf.v[i - 1].last + 1 : 0;
		}
		mf_expect("reverse walk", entry, want);
		if (mas.index != want_start || mas.last != pos)
			mf_fail("reverse walk: range %llx-%llx want %llx-%llx",
				(unsigned long long)mas.index,
				(unsigned long long)mas.last,
				(unsigned long long)want_start,
				(unsigned long long)pos);
		if (!want_start)
			break;
		pos = want_start - 1;
		entry = mas_prev_range(&mas, 0);
		if (!mas_is_active(&mas))
			mf_fail("reverse walk: tree ended at %llx",
				(unsigned long long)pos);
	}
	rcu_read_unlock();
}

static void mf_check_loads(void)
{
	u64 ceiling = mf_ceiling();
	unsigned int k;

	for (k = 0; k < 64; k++) {
		u64 idx = mf_probe(ceiling);
		struct mf_ival *iv;
		void *entry;
		MA_STATE(mas, &mf.mt, 0, 0);

		/* The ceiling, the index above it and the top, every pass. */
		if (k == 0)
			idx = ceiling;
		else if (k == 1 && ceiling < U64_MAX)
			idx = ceiling + 1;
		else if (k == 2)
			idx = U64_MAX;
		iv = model_find(idx);
		mf_expect("load", mtree_load_u64(&mf.mt, idx),
			  iv ? iv->vma : NULL);

		rcu_read_lock();
		mas_set(&mas, idx);
		entry = mas_walk(&mas);
		mf_expect("walk", entry, iv ? iv->vma : NULL);
		if (iv)
			mf_expect_range("walk", &mas, iv->start, iv->last);
		else
			mf_expect_gap("walk", &mas, idx);
		rcu_read_unlock();
	}
}

/* The top of the index space: backwards from it, and an iterator run past. */
static void mf_check_top(void)
{
	struct mf_ival *last = mf.n ? &mf.v[mf.n - 1] : NULL;
	MA_STATE(mas, &mf.mt, U64_MAX, U64_MAX);

	rcu_read_lock();
	mf_expect("find_rev top", mas_find_rev(&mas, 0), last ? last->vma : NULL);
	if (last)
		mf_expect_range("find_rev top", &mas, last->start, last->last);

	if (last && last->last < U64_MAX) {
		mas_set(&mas, U64_MAX);
		mf_expect("prev top", mas_prev(&mas, 0), last->vma);
		mf_expect_range("prev top", &mas, last->start, last->last);

		/* A paused iterator resumes past the last entry, then steps back. */
		mas_set(&mas, last->start);
		mf_expect("find last", mas_find(&mas, U64_MAX), last->vma);
		mas_pause(&mas);
		mf_expect("find past last", mas_find(&mas, U64_MAX), NULL);
		mf_expect("prev past last", mas_prev(&mas, 0), last->vma);
		mf_expect_range("prev past last", &mas, last->start, last->last);
	}
	rcu_read_unlock();
}

static void mf_check_gaps(void)
{
	unsigned int k;

	for (k = 0; k < 32; k++) {
		u64 lo = mf_addr();
		u64 hi = mf_chance(30) ? U64_MAX : mf_addr() | (mf.unit - 1);
		u64 size = mf_chance(20) ? mf_rand() : mf_size();
		u64 eidx, elast;
		bool down = k & 1, found;
		int ret;
		MA_STATE(mas, &mf.mt, 0, 0);

		if (lo > hi) {
			u64 t = lo;

			lo = hi;
			hi = t;
		}
		if (!size || hi - lo < size - 1)
			continue;

		mtree_lock(&mf.mt);
		if (down)
			ret = mas_empty_area_rev(&mas, lo, hi, size);
		else
			ret = mas_empty_area(&mas, lo, hi, size);
		found = model_gap(lo, hi, size, !down, &eidx, &elast);
		if (ret != 0 && ret != -EBUSY)
			mf_fail("gap check: ret %d", ret);
		if ((ret == 0) != found)
			mf_fail("gap check %llx-%llx size %llx %s: ret %d, model %sfound",
				(unsigned long long)lo, (unsigned long long)hi,
				(unsigned long long)size, down ? "rev" : "fwd",
				ret, found ? "" : "not ");
		if (found) {
			size_t i;
			void *n;

			mf_expect_range("gap check", &mas, eidx, elast);
			i = model_first_after(elast == U64_MAX ? elast :
							       elast + 1);
			n = mas_find(&mas, U64_MAX);
			mf_expect("gap check next", n,
				  (elast != U64_MAX && i < mf.n) ?
				  mf.v[i].vma : NULL);
			if (n)
				mf_expect("gap check prev", mas_prev(&mas, 0),
					  i ? mf.v[i - 1].vma : NULL);
		}
		mas_destroy(&mas);
		mtree_unlock(&mf.mt);
	}
}

/* Every marked range, both ways, then random windows, against the model. */
static void mf_check_marks(void)
{
	u64 ceiling = mf_ceiling();
	unsigned int k;
	mt_mark_t mark;

	for (mark = 0; mark <= MT_MARK_MAX; mark++) {
		MA_STATE(mas, &mf.mt, 0, 0);
		size_t i = 0;
		bool any = false;
		void *entry;

		rcu_read_lock();
		mas_for_each_marked(&mas, entry, U64_MAX, mark) {
			while (i < mf.n && !(mf.v[i].marks & BIT(mark)))
				i++;
			if (i == mf.n)
				mf_fail("marked walk: mark %u at %llx not in the model",
					mark, (unsigned long long)mas.index);
			mf_expect("marked walk", entry, mf.v[i].vma);
			mf_expect_range("marked walk", &mas, mf.v[i].start,
					mf.v[i].last);
			any = true;
			i++;
		}
		while (i < mf.n && !(mf.v[i].marks & BIT(mark)))
			i++;
		if (i < mf.n)
			mf_fail("marked walk: mark %u missed %llx", mark,
				(unsigned long long)mf.v[i].start);

		mas_set(&mas, ceiling);
		i = mf.n;
		mas_for_each_marked_rev(&mas, entry, 0, mark) {
			while (i && !(mf.v[i - 1].marks & BIT(mark)))
				i--;
			if (!i)
				mf_fail("marked walk rev: mark %u at %llx not in the model",
					mark, (unsigned long long)mas.index);
			i--;
			mf_expect("marked walk rev", entry, mf.v[i].vma);
			mf_expect_range("marked walk rev", &mas, mf.v[i].start,
					mf.v[i].last);
		}
		while (i && !(mf.v[i - 1].marks & BIT(mark)))
			i--;
		if (i)
			mf_fail("marked walk rev: mark %u missed %llx", mark,
				(unsigned long long)mf.v[i - 1].start);
		rcu_read_unlock();

		if (mt_marked(&mf.mt, mark) != any)
			mf_fail("mt_marked %u disagrees with the model", mark);
	}

	for (k = 0; k < 32; k++) {
		u64 idx = mf_probe(ceiling);
		u64 lim = mf_chance(30) ? (k & 1 ? 0 : U64_MAX) : mf_probe(ceiling);
		struct mf_ival *want;
		void *entry;
		MA_STATE(mas, &mf.mt, idx, idx);

		mark = mf_rand_below(MT_MARK_MAX + 1);
		rcu_read_lock();
		if (k & 1) {
			if (lim > idx)
				lim = idx;
			want = model_marked_before(idx, lim, mark);
			entry = mas_find_marked_rev(&mas, lim, mark);
		} else {
			if (lim < idx)
				lim = idx;
			want = model_marked_after(idx, lim, mark);
			entry = mas_find_marked(&mas, lim, mark);
		}
		mf_expect(k & 1 ? "find marked rev" : "find marked", entry,
			  want ? want->vma : NULL);
		if (want)
			mf_expect_range(k & 1 ? "find marked rev" : "find marked",
					&mas, want->start, want->last);
		rcu_read_unlock();
	}
}

/* Every node the tree reaches, in the order mt_validate() uses. */
static unsigned int mf_count_nodes(struct maple_tree *mt)
{
	unsigned int count = 0;
	MA_STATE(mas, mt, 0, 0);

	mas_start(&mas);
	if (!mas_is_active(&mas))
		return 0;

	while (!mte_is_leaf(mas.node))
		mas_descend(&mas);

	while (!mas_is_overflow(&mas)) {
		count++;
		mas_dfs_postorder(&mas, U64_MAX);
	}
	return count;
}

static unsigned int mf_count_dense(void)
{
	unsigned int count = 0;
	MA_STATE(mas, &mf.mt, 0, 0);

	mtree_lock(&mf.mt);
	mas_start(&mas);
	if (mas_is_active(&mas)) {
		while (!mte_is_leaf(mas.node))
			mas_descend(&mas);
		while (!mas_is_overflow(&mas)) {
			if (ma_is_dense(mas_node_type(&mas, mas.node)))
				count++;
			mas_dfs_postorder(&mas, U64_MAX);
		}
	}
	mtree_unlock(&mf.mt);
	return count;
}

/* Nothing but the tree holds nodes between operations. */
static void mf_check_leak(const char *what)
{
	unsigned int in_tree, allocated;

	rcu_barrier();
	mtree_lock(&mf.mt);
	in_tree = mf_count_nodes(&mf.mt);
	mtree_unlock(&mf.mt);
	allocated = mt_nr_allocated();
	if (allocated != in_tree)
		mf_fail("%s: %u nodes allocated, %u in the tree", what,
			allocated, in_tree);
}

/* Node sizes, pivots, parent slots, gaps and NULL bits. */
static void mf_check_structure(void)
{
	mtree_lock(&mf.mt);
	mt_validate(&mf.mt);
	mtree_unlock(&mf.mt);
	mf.rebuilt = false;
	mf.since = 0;
}

static void mf_validate(void)
{
	mf_check_structure();
	mf_check_forward(&mf.mt);
	if (!(mf.pass % 4))
		mf_check_reverse(&mf.mt);
	mf_check_loads();
	mf_check_top();
	mf_check_gaps();
	mf_check_marks();
	mf_check_leak("pass");
}

/* Read operations */

static void op_load(void)
{
	u64 idx = mf_probe(mf_ceiling());
	struct mf_ival *iv = model_find(idx);

	mf_record(MF_LOAD, idx, 0, 0);
	mf_expect("load", mtree_load_u64(&mf.mt, idx), iv ? iv->vma : NULL);
}

static void op_walk(void)
{
	u64 idx = mf_probe(mf_ceiling());
	struct mf_ival *iv = model_find(idx);
	MA_STATE(mas, &mf.mt, idx, idx);

	mf_record(MF_WALK, idx, 0, 0);
	rcu_read_lock();
	mf_expect("walk", mas_walk(&mas), iv ? iv->vma : NULL);
	if (iv)
		mf_expect_range("walk", &mas, iv->start, iv->last);
	rcu_read_unlock();
}

/*
 * A chain of find/next/prev steps from a random anchor, checked step by step
 * against the model.  The chain stops at the first NULL, before the
 * overflow and underflow states need modelling.
 */
static void op_chain(void)
{
	u64 idx = mf_probe(mf_ceiling());
	u64 hi = mf_chance(50) ? U64_MAX : mf_addr();
	u64 lo = mf_chance(50) ? 0 : mf_addr();
	size_t cur;
	unsigned int steps = 1 + mf_rand_below(8), k;
	void *entry;
	MA_STATE(mas, &mf.mt, idx, idx);

	if (hi < idx)
		hi = idx;
	if (lo > idx)
		lo = idx;
	mf_record(MF_CHAIN, idx, lo, hi);

	rcu_read_lock();
	/* mas_find(): the range holding idx, else the next one up to hi. */
	cur = model_first_after(idx);
	entry = mas_find(&mas, hi);
	if (cur < mf.n && mf.v[cur].start <= hi) {
		mf_expect("chain find", entry, mf.v[cur].vma);
		mf_expect_range("chain find", &mas, mf.v[cur].start,
				mf.v[cur].last);
	} else {
		mf_expect("chain find", entry, NULL);
		goto out;
	}

	for (k = 0; k < steps; k++) {
		size_t want;
		bool fwd = mf_chance(60);

		if (mf_chance(10))
			mas_pause(&mas);

		if (fwd) {
			want = cur + 1;
			entry = mf_chance(50) ? mas_next(&mas, hi) :
						mas_find(&mas, hi);
			if (mf.v[cur].last >= hi || want >= mf.n ||
			    mf.v[want].start > hi) {
				mf_expect("chain next", entry, NULL);
				goto out;
			}
		} else {
			entry = mas_prev(&mas, lo);
			if (mf.v[cur].start <= lo || !cur ||
			    mf.v[cur - 1].last < lo) {
				mf_expect("chain prev", entry, NULL);
				goto out;
			}
			want = cur - 1;
		}
		mf_expect(fwd ? "chain next" : "chain prev", entry,
			  mf.v[want].vma);
		mf_expect_range(fwd ? "chain next" : "chain prev", &mas,
				mf.v[want].start, mf.v[want].last);
		cur = want;
	}
out:
	rcu_read_unlock();
}

/* mas_next_range() over a window, NULL ranges included. */
static void op_ranges(void)
{
	u64 ceiling = mf_ceiling();
	u64 a = mf_probe(ceiling), b = mf_probe(ceiling);
	size_t i;
	u64 pos;
	void *entry;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (a > b) {
		u64 t = a;

		a = b;
		b = t;
	}
	mf_record(MF_RANGES, a, b, 0);

	rcu_read_lock();
	mas_set(&mas, a);
	entry = mas_walk(&mas);
	i = model_first_after(a);
	pos = (i < mf.n && mf.v[i].start <= a) ? mf.v[i].start :
	      (i ? mf.v[i - 1].last + 1 : 0);
	/* Above the ceiling only the gap from the ceiling up is seen. */
	if (a > ceiling)
		pos = ceiling + 1;
	for (;;) {
		struct mf_vma *want;
		u64 want_last;

		if (i < mf.n && mf.v[i].start == pos) {
			want = mf.v[i].vma;
			want_last = mf.v[i].last;
			i++;
		} else {
			want = NULL;
			want_last = (i < mf.n) ? mf.v[i].start - 1 : U64_MAX;
			if (want_last == U64_MAX)
				want_last = mas_is_active(&mas) ?
					    mas_tree_max(&mas) : ULONG_MAX;
		}
		mf_expect("ranges", entry, want);
		mf_expect_range("ranges", &mas, pos, want_last);
		/* The tree ends at its ceiling; the next range would overflow. */
		if (want_last >= b || want_last >= ceiling || !mas_is_active(&mas))
			break;
		pos = want_last + 1;
		entry = mas_next_range(&mas, b);
		if (!mas_is_active(&mas))
			mf_fail("ranges: tree ended at %llx",
				(unsigned long long)pos);
	}
	rcu_read_unlock();
}

/* Occasional operations */

static void mf_build(void)
{
	size_t i;
	mt_mark_t mark;

	for (i = 0; i < mf.n; i++) {
		MA_STATE(mas, &mf.mt, mf.v[i].start, mf.v[i].last);

		mtree_lock(&mf.mt);
		mf_prealloc_store(&mas, mf.v[i].vma);
		mas_destroy(&mas);
		for (mark = 0; mark <= MT_MARK_MAX; mark++) {
			if (!(mf.v[i].marks & BIT(mark)))
				continue;
			mas_set(&mas, mf.v[i].start);
			mas_set_mark(&mas, mark);
		}
		mtree_unlock(&mf.mt);
	}
}

/*
 * Empty the tree and rebuild it, so it is born 32-bit again.  Not with
 * readers: they bound their reads by a ceiling that must not drop.
 */
static void op_reset(void)
{
	struct mf_ival *snap;
	size_t n = mf.n, i;
	int ret;
	MA_STATE(mas, &mf.mt, 0, 0);

	if (mf.nreaders)
		return;
	mf_record(MF_RESET, n, 0, 0);
	snap = malloc(n * sizeof(*snap) + 1);
	if (!snap)
		mf_fail("malloc");
	memcpy(snap, mf.v, n * sizeof(*snap));

	mtree_lock(&mf.mt);
	mas_set_range(&mas, 0, U64_MAX);
	ret = mas_store_gfp(&mas, NULL, GFP_KERNEL);
	if (ret)
		mf_fail("mas_store_gfp %d", ret);
	mf_tally(&mas);
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
	mf.n = 0;

	rcu_barrier();
	if (mt_nr_allocated())
		mf_fail("reset: %u nodes still allocated", mt_nr_allocated());

	for (i = 0; i < n; i++)
		model_insert(i, snap[i].start, snap[i].last, snap[i].vma,
			     snap[i].marks);
	free(snap);
	mf_build();
}

/* dup_mmap(): copy the tree, store over every entry, check, destroy. */
static void op_fork(void)
{
	struct maple_tree mt2;
	void *entry;
	int ret;
	MA_STATE(mas, &mt2, 0, 0);

	mf_record(MF_FORK, mf.n, 0, 0);
	mt_init(&mt2);
	mt_init_flags(&mt2, mt_attr(&mf.mt));
	ret = mtree_dup(&mf.mt, &mt2, GFP_KERNEL);
	if (ret)
		mf_fail("mtree_dup %d", ret);

	mtree_lock(&mt2);
	mas_for_each(&mas, entry, U64_MAX) {
		u64 start = mas.index, last = mas.last;

		do {
			mas_store(&mas, entry);
			if (!mas_is_err(&mas))
				break;
			mas_nomem(&mas, GFP_KERNEL);
			__mas_set_range(&mas, start, last);
		} while (1);
		mf_tally(&mas);
	}
	mas_destroy(&mas);
	mt_validate(&mt2);
	mtree_unlock(&mt2);
	mf_check_forward(&mt2);
	mtree_destroy(&mt2);
	rcu_barrier();
}

static void op_rcu(void)
{
	bool external = mt_external_lock(&mf.mt);

	if (mf.nreaders)
		return;
	mf_record(MF_RCU, !mt_in_rcu(&mf.mt), 0, 0);
	if (external)
		mtree_lock(&mf.mt);
	if (mt_in_rcu(&mf.mt))
		mt_clear_in_rcu(&mf.mt);
	else
		mt_set_in_rcu(&mf.mt);
	if (external)
		mtree_unlock(&mf.mt);
}

static void op_nonkernel(void)
{
	unsigned int credits = mf_rand_below(65);

	mf_record(MF_NONKERNEL, credits, 0, 0);
	mt_set_non_kernel(credits);
}

/*
 * Directed stores.  Each builds the shape with the same stores the random
 * operations use, then asserts the store type of the final one.
 */

/* Split a range inside [lo, hi] at @mas; false when none is wide enough. */
static bool mf_split_within(struct ma_state *mas, u64 lo, u64 hi,
			    enum store_type *type)
{
	void *entry;

	mas_set(mas, lo);
	entry = mas_walk(mas);
	while (mas_is_active(mas) && mas->index <= hi) {
		u64 rs = mas->index, rl = mas->last < hi ? mas->last : hi;

		if (rl - rs + 1 >= 2 * mf.unit) {
			u64 cut = rs + mf_align((rl - rs + 1) / 2);
			struct mf_vma *vma = mf_vma_new();
			int ret;

			if (cut <= rs)
				cut = rs + mf.unit;
			__mas_set_range(mas, cut, rl);
			ret = mas_preallocate(mas, vma, GFP_KERNEL);
			if (ret)
				mf_fail("mas_preallocate %d", ret);
			*type = mas->store_type;
			mf_tally(mas);
			mas_store_prealloc(mas, vma);
			model_store(cut, rl, vma);
			return true;
		}
		if (mas->last >= hi)
			break;
		entry = mas_next_range(mas, hi);
	}
	(void)entry;
	return false;
}

static bool mf_directed_split(void)
{
	unsigned int attempt;

	for (attempt = 0; attempt < 16 && mf.n; attempt++) {
		struct mf_ival iv = mf.v[mf_rand_below(mf.n)];
		enum store_type type = wr_invalid;
		u64 lo, hi;
		unsigned char slots;
		bool full = false, done;
		MA_STATE(mas, &mf.mt, 0, 0);

		mf_record(MF_DIRECTED, wr_split_store, iv.start, 0);
		mtree_lock(&mf.mt);
		mas_set(&mas, iv.start);
		if (!mas_walk(&mas) ||
		    ma_is_dense(mas_node_type(&mas, mas.node))) {
			mtree_unlock(&mf.mt);
			continue;
		}
		lo = mas.min;
		hi = mas.max;
		slots = mas_slot_count(&mas, mas.node);

		/* Fill the leaf with node stores, then one store more. */
		for (;;) {
			mas_set(&mas, lo);
			mas_walk(&mas);
			if (mas.min != lo || mas.max != hi)
				break;
			full = mas_data_end(&mas) >= slots - 1;
			done = !mf_split_within(&mas, lo, hi, &type);
			if (full || done)
				break;
		}
		mas_destroy(&mas);
		mtree_unlock(&mf.mt);
		if (full && type == wr_split_store)
			return true;
	}
	return false;
}

static bool mf_directed_spanning(void)
{
	u64 ceiling = mf_ceiling();
	u64 cs = 0, cl = 0, ns = 0, nl = 0;
	unsigned int seen = 0;
	void *entry;
	MA_STATE(mas, &mf.mt, 0, 0);

	mf_record(MF_DIRECTED, wr_spanning_store, 0, 0);
	mtree_lock(&mf.mt);
	mas_set(&mas, 0);
	entry = mas_walk(&mas);
	/* Pick, at random, a range ending its leaf and the range after it. */
	while (mas_is_active(&mas) && mas.last < ceiling) {
		u64 s = mas.index, l = mas.last;
		bool edge = mas.offset == mas.end &&
			    !ma_is_dense(mas_node_type(&mas, mas.node));

		entry = mas_next_range(&mas, U64_MAX);
		if (!mas_is_active(&mas))
			break;
		if (edge && !mf_rand_below(++seen)) {
			cs = s;
			cl = l;
			ns = mas.index;
			nl = mas.last;
		}
	}
	(void)entry;

	if (seen) {
		u64 start = (cl - cs + 1 > mf.unit) ? cl - mf.unit + 1 : cs;
		u64 last = (nl - ns + 1 > mf.unit) ? ns + mf.unit - 1 : nl;
		struct mf_vma *vma = mf_vma_new();
		enum store_type type;
		int ret;

		mas_set(&mas, start);
		mas_walk(&mas);
		__mas_set_range(&mas, start, last);
		ret = mas_preallocate(&mas, vma, GFP_KERNEL);
		if (ret)
			mf_fail("mas_preallocate %d", ret);
		type = mas.store_type;
		mf_tally(&mas);
		mas_store_prealloc(&mas, vma);
		model_store(start, last, vma);
		mas_destroy(&mas);
		mtree_unlock(&mf.mt);
		return type == wr_spanning_store;
	}
	mas_destroy(&mas);
	mtree_unlock(&mf.mt);
	return false;
}

static bool mf_directed_rebalance(void)
{
	unsigned int attempt;

	for (attempt = 0; attempt < 16 && mf.n; attempt++) {
		struct mf_ival iv = mf.v[mf_rand_below(mf.n)];
		enum store_type type = wr_invalid;
		u64 lo, hi;
		MA_STATE(mas, &mf.mt, 0, 0);

		mf_record(MF_DIRECTED, wr_rebalance, iv.start, 0);
		mtree_lock(&mf.mt);
		mas_set(&mas, iv.start);
		if (!mas_walk(&mas) || mte_is_root(mas.node) ||
		    ma_is_dense(mas_node_type(&mas, mas.node))) {
			mtree_unlock(&mf.mt);
			continue;
		}
		lo = mas.min;
		hi = mas.max;

		/* Merge the leaf's first two ranges until it is insufficient. */
		for (;;) {
			u64 r0s, r1l;
			struct mf_vma *vma;
			int ret;

			mas_set(&mas, lo);
			mas_walk(&mas);
			if (mas.min != lo || mas.max != hi ||
			    mas_data_end(&mas) < 1)
				break;
			r0s = mas.index;
			mas_next_range(&mas, hi);
			r1l = mas.last;
			mas_set(&mas, lo);
			mas_walk(&mas);
			vma = mf_vma_new();
			__mas_set_range(&mas, r0s, r1l);
			ret = mas_preallocate(&mas, vma, GFP_KERNEL);
			if (ret)
				mf_fail("mas_preallocate %d", ret);
			type = mas.store_type;
			mf_tally(&mas);
			mas_store_prealloc(&mas, vma);
			model_store(r0s, r1l, vma);
			if (type != wr_node_store && type != wr_slot_store)
				break;
		}
		mas_destroy(&mas);
		mtree_unlock(&mf.mt);
		if (type == wr_rebalance)
			return true;
	}
	return false;
}

static void mf_single(u64 idx)
{
	struct mf_vma *vma = mf_vma_new();
	int ret = mtree_store_range_u64(&mf.mt, idx, idx, vma, GFP_KERNEL);

	if (ret)
		mf_fail("mtree_store_range_u64 %d", ret);
	model_store(idx, idx, vma);
}

/*
 * A dense leaf takes a leaf narrower than its slots holding more entries than
 * a range leaf.  Singles every few indices over a window leave the splits with
 * narrow leaves; filling every index then overflows them one by one.  The
 * stride sets the width of those leaves, so a few are tried.
 */
static bool mf_directed_dense(void)
{
	static const unsigned char strides[] = { 4, 3, 5, 6 };
	u64 w = 8 * mt_slots[maple_dense], b, last, i;
	unsigned int s;

	for (s = 0; s < ARRAY_SIZE(strides); s++) {
		if (!model_gap(mf_addr(), mf.top, w, true, &b, &last) &&
		    !model_gap(mf.floor, mf.top, w, true, &b, &last))
			return false;
		mf_record(MF_DIRECTED, wr_invalid, b, strides[s]);
		for (i = b; i < b + w; i += strides[s])
			mf_single(i);
		for (i = b; i < b + w; i++)
			if (!model_find(i))
				mf_single(i);
		if (mf_count_dense())
			return true;
	}
	return false;
}

static void mf_ensure_coverage(void)
{
	if (!mf.hist[wr_split_store] && !mf_directed_split())
		mf_fail("no split store in this pass");
	if (mf.pfn && !mf_count_dense() && !mf_directed_dense())
		mf_fail("no dense leaf in this pass");
	if (mt_height(&mf.mt) < 2) {
		if (mf.verbose)
			fprintf(stderr, "pass %u: one node, no spanning or rebalance\n",
				mf.pass);
		return;
	}
	if (!mf.hist[wr_spanning_store] && !mf_directed_spanning())
		mf_fail("no spanning store in this pass");
	if (!mf.hist[wr_rebalance] && !mf_directed_rebalance())
		mf_fail("no rebalance in this pass");
}

/* Input */

static void mf_add_range(u64 start, u64 last)
{
	size_t i = model_first_after(start);

	if (i < mf.n && mf.v[i].start <= last) {
		fprintf(stderr, "maple-fuzz: skipping %llx-%llx, overlaps\n",
			(unsigned long long)start, (unsigned long long)last);
		return;
	}
	model_insert(i, start, last, mf_vma_new(), 0);
}

static void mf_read_maps(const char *path)
{
	FILE *f = fopen(path, "r");
	char line[512];

	if (!f) {
		fprintf(stderr, "maple-fuzz: %s: %s\n", path, strerror(errno));
		exit(1);
	}
	while (fgets(line, sizeof(line), f)) {
		unsigned long long s, e;

		if (sscanf(line, "%llx-%llx", &s, &e) != 2)
			continue;
		if (mf.pfn) {
			s >>= MF_PAGE_SHIFT;
			e >>= MF_PAGE_SHIFT;
		}
		if (e <= s || e - 1 > mf.top || s < mf.floor) {
			fprintf(stderr, "maple-fuzz: skipping %s", line);
			continue;
		}
		mf_add_range(s, e - 1);
	}
	fclose(f);
}

/* Place @count ranges below @hi, clustered low, high and scattered. */
static void mf_generate(u64 count, u64 hi)
{
	u64 k;

	if (hi < mf.floor)
		return;
	for (k = 0; k < count; k++) {
		u64 size = mf_size(), lo = mf.floor, idx, last;
		bool lowest = true;

		switch (mf_rand_below(4)) {
		case 0:
			break;
		case 1:
			lowest = false;
			break;
		default:
			lo = mf.floor + mf_align(mf_rand_below(hi - mf.floor + 1));
			break;
		}
		if (size - 1 > hi - mf.floor)
			size = mf.unit;
		if (!model_gap(lo, hi, size, lowest, &idx, &last) &&
		    !model_gap(mf.floor, hi, size, true, &idx, &last))
			return;
		mf_add_range(idx, last);
	}
}

static void mf_print_maps(FILE *f)
{
	size_t i;

	for (i = 0; i < mf.n; i++) {
		unsigned long long s = mf.v[i].start, e = mf.v[i].last + 1;

		if (mf.pfn) {
			s <<= MF_PAGE_SHIFT;
			e <<= MF_PAGE_SHIFT;
		}
		fprintf(f, "%llx-%llx rw-p 00000000 00:00 0\n", s, e);
	}
}

static void mf_usage(void)
{
	fprintf(stderr,
		"usage: maple-fuzz [-m maps | -g count] [-t top] [-F floor] [-s seed]\n"
		"                  [-n passes, 0 forever] [-o ops-per-pass] [-p] [-b N]\n"
		"                  [-P passes] [-f alloc|plain|marks] [-a] [-A configs]\n"
		"                  [-r readers] [-R] [-L] [-l] [-v] [-W file] [-c file]\n"
		"  -g  ranges to generate; the run then keeps the model near that many\n"
		"  -F  lowest address; above 4G the tree is born 64-bit\n"
		"  -P  build below 4G and lift the top after this many passes\n"
		"  -p  indices are page frame numbers, so single pages make dense leaves\n"
		"  -a  sweep alloc, range and marks trees, with and without -p and RCU\n"
		"  -A  stop the sweep after this many configurations, for a replay\n"
		"  -r  RCU reader threads during the operations (no reset, no -R)\n"
		"  -l  check for leaked nodes after every operation\n"
		"  -c  the full failure report, default maple-fuzz-crash.txt\n");
	exit(2);
}

/*
 * RCU readers.  They have no model to compare with while the writer runs, so
 * they check what a walk promises: forward progress, sane ranges, live entries.
 * The ceiling of a born-32 tree bounds their reads; it only rises without
 * resets, so a stale one is safe.
 */
struct mf_reader {
	pthread_t thread;
	u64 rng;
};

static struct mf_reader *mf_readers;
static volatile bool mf_readers_on;

/* The first reader failure; the writer reports it between operations. */
static char mf_reader_msg[128];

static void __attribute__((format(printf, 1, 2)))
mf_reader_fail(const char *fmt, ...)
{
	static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
	va_list ap;

	pthread_mutex_lock(&lock);
	if (!mf_reader_msg[0]) {
		va_start(ap, fmt);
		vsnprintf(mf_reader_msg, sizeof(mf_reader_msg), fmt, ap);
		va_end(ap);
	}
	mf_readers_on = false;
	pthread_mutex_unlock(&lock);
}

static bool mf_reader_entry(void *entry, u64 index, u64 last)
{
	struct mf_vma *v = entry;

	if (index <= last && (!v || v->id))
		return true;

	mf_reader_fail("reader: %llx-%llx id %u", (unsigned long long)index,
		       (unsigned long long)last, v ? v->id : 0);
	return false;
}

/*
 * A store can replace the nodes under a chain.  The next step then lands on
 * the new entry holding the old position, which may start before what was
 * already seen, so progress is measured by the end going forward and the
 * start going back.
 */
static void mf_reader_once(struct mf_reader *rd)
{
	u64 ceiling, idx, prev = 0;
	unsigned int steps = 1 + mf_rand_r(&rd->rng) % 64, k;
	mt_mark_t mark = mf_rand_r(&rd->rng) % (MT_MARK_MAX + 1);
	void *entry;
	MA_STATE(mas, &mf.mt, 0, 0);

	rcu_read_lock();
	mas_walk(&mas);
	ceiling = mas_is_active(&mas) ? mas_tree_max(&mas) : U64_MAX;
	if (ceiling > mf.top)
		ceiling = mf.top;
	idx = mf_align(mf_rand_r(&rd->rng) % (ceiling + 1));
	mas_set(&mas, idx);
	switch (mf_rand_r(&rd->rng) % 4) {
	case 0:
		mf_reader_entry(mtree_load_u64(&mf.mt, idx), idx, idx);
		break;
	case 1:
		for (k = 0; k < steps; k++) {
			entry = mas_find(&mas, ceiling);
			if (!entry)
				break;
			if (k && mas.last < prev) {
				mf_reader_fail("reader: find went back to %llx from %llx",
					       (unsigned long long)mas.last,
					       (unsigned long long)prev);
				break;
			}
			if (!mf_reader_entry(entry, mas.index, mas.last))
				break;
			prev = mas.last;
		}
		break;
	case 2:
		for (k = 0; k < steps; k++) {
			entry = mas_find_rev(&mas, 0);
			if (!entry)
				break;
			if (k && mas.index > prev) {
				mf_reader_fail("reader: find_rev went on to %llx from %llx",
					       (unsigned long long)mas.index,
					       (unsigned long long)prev);
				break;
			}
			if (!mf_reader_entry(entry, mas.index, mas.last))
				break;
			prev = mas.index;
		}
		break;
	default:
		for (k = 0; k < steps; k++) {
			entry = mas_find_marked(&mas, ceiling, mark);
			if (!entry)
				break;
			if (k && mas.last < prev) {
				mf_reader_fail("reader: find_marked went back to %llx from %llx",
					       (unsigned long long)mas.last,
					       (unsigned long long)prev);
				break;
			}
			if (!mf_reader_entry(entry, mas.index, mas.last))
				break;
			prev = mas.last;
		}
		break;
	}
	rcu_read_unlock();
}

static void *mf_reader_run(void *arg)
{
	struct mf_reader *rd = arg;

	rcu_register_thread();
	while (mf_readers_on)
		mf_reader_once(rd);
	rcu_unregister_thread();
	return NULL;
}

static void mf_readers_start(void)
{
	unsigned int i;

	mf_readers_on = true;
	for (i = 0; i < mf.nreaders; i++)
		if (pthread_create(&mf_readers[i].thread, NULL, mf_reader_run,
				   &mf_readers[i]))
			mf_fail("pthread_create");
}

static void mf_readers_stop(void)
{
	unsigned int i;

	mf_readers_on = false;
	for (i = 0; i < mf.nreaders; i++)
		pthread_join(mf_readers[i].thread, NULL);
	if (mf_reader_msg[0])
		mf_fail("%s", mf_reader_msg);
}

/* A warning nobody expected fails the run where it showed up. */
static void mf_check_warnings(void)
{
	if (mt_unexpected)
		mf_fail("%u unexpected warnings", mt_unexpected);
}

static void mf_pass(void)
{
	unsigned int k, h;

	memset(mf.hist, 0, sizeof(mf.hist));
	mf_readers_start();
	for (k = 0; k < mf.ops; k++) {
		unsigned int r = mf_rand_below(100), op;

		/* Reported here, with the tree and the model at rest. */
		if (mf_reader_msg[0])
			mf_fail("%s", mf_reader_msg);

		for (op = 0; op < MF_NR_OPS - 1; op++) {
			if (r < mf_op_weight[op])
				break;
			r -= mf_op_weight[op];
		}
		switch (op) {
		case MF_MMAP_UP:
			op_mmap(false);
			break;
		case MF_MMAP_DOWN:
			op_mmap(true);
			break;
		case MF_MMAP_FIXED:
			op_mmap_fixed();
			break;
		case MF_MUNMAP:
			op_munmap();
			break;
		case MF_SPLIT:
			op_split();
			break;
		case MF_MERGE:
			op_merge();
			break;
		case MF_EXPAND:
			op_expand();
			break;
		case MF_SHRINK:
			op_shrink();
			break;
		case MF_MOVE:
			op_move();
			break;
		case MF_BRK:
			op_brk();
			break;
		case MF_ERASE:
			op_erase();
			break;
		case MF_SIMPLE:
			op_simple();
			break;
		case MF_FORK:
			op_fork();
			break;
		case MF_RESET:
			op_reset();
			break;
		case MF_RCU:
			op_rcu();
			break;
		case MF_NONKERNEL:
			op_nonkernel();
			break;
		case MF_LOAD:
			op_load();
			break;
		case MF_WALK:
			op_walk();
			break;
		case MF_CHAIN:
			op_chain();
			break;
		case MF_RANGES:
			op_ranges();
			break;
		case MF_MARK:
			op_mark();
			break;
		case MF_ALLOC:
			op_alloc();
			break;
		default:
			mf_record(MF_GAP, 0, 0, 0);
			mf_check_gaps();
			break;
		}
		mf_check_warnings();
		/* Not after every op, but before the one that broke it leaves the ring. */
		mf.since++;
		if (mf.rebuilt && mf.since >= MF_CHECK_EVERY)
			mf_check_structure();
		if (mf.leak)
			mf_check_leak(mf_op_name[op]);
	}

	mf_ensure_coverage();
	mf_readers_stop();
	mf_validate();
	mf_sweep_vmas();
	mf_check_warnings();
	h = mt_height(&mf.mt);
	if (mf.pass == 1 || h < mf.hmin)
		mf.hmin = h;
	if (mf.pass == 1 || h > mf.hmax)
		mf.hmax = h;
	if (mf.pass == 1 || mf.n < mf.nmin)
		mf.nmin = mf.n;
	if (mf.pass == 1 || mf.n > mf.nmax)
		mf.nmax = mf.n;
	if (mf.verbose) {
		fprintf(stderr, "pass %u: %zu ranges, height %u, nodes %u, dense %u, stores:",
			mf.pass, mf.n, h, mt_nr_allocated(), mf_count_dense());
		for (k = 1; k < MF_NR_STORE; k++)
			fprintf(stderr, " %s=%u", mf_store_name[k], mf.hist[k]);
		fprintf(stderr, "\n");
	}
}

/* One tree: build the space, run the passes, tear it down. */
static void mf_run(unsigned int flags, bool pfn, unsigned int passes)
{
	u64 full;
	size_t i;

	mf.pfn = pfn;
	mf.unit = pfn ? 1 : (u64)1 << MF_PAGE_SHIFT;
	mf.top = pfn ? mf.top_arg >> MF_PAGE_SHIFT : mf.top_arg;
	mf.top = mf_align(mf.top + 1) - 1;
	mf.floor = mf_align(pfn ? mf.floor_arg >> MF_PAGE_SHIFT : mf.floor_arg);
	if (mf.floor > mf.top) {
		fprintf(stderr, "maple-fuzz: floor above top\n");
		exit(1);
	}
	/* Built below the 4G seam, the top is lifted after -P passes. */
	full = mf.top;
	if (mf.promote) {
		u64 seam = pfn ? (u64)U32_MAX >> MF_PAGE_SHIFT : U32_MAX;

		if (mf.floor <= seam && mf.top > seam)
			mf.top = seam;
	}
	mt_init(&mf.mt);
	mt_init_flags(&mf.mt, flags);

	if (mf.maps)
		mf_read_maps(mf.maps);
	else
		mf_generate(mf.gen, mf.top);
	if (mf.below4g) {
		u64 hi = (u64)U32_MAX;

		if (mf.pfn)
			hi >>= MF_PAGE_SHIFT;
		mf_generate(mf.below4g, hi < mf.top ? hi : mf.top);
	}
	if (!mf.n) {
		fprintf(stderr, "maple-fuzz: no ranges\n");
		exit(1);
	}
	if (mf.save) {
		FILE *f = fopen(mf.save, "w");

		if (!f) {
			fprintf(stderr, "maple-fuzz: %s: %s\n", mf.save,
				strerror(errno));
			exit(1);
		}
		mf_print_maps(f);
		fclose(f);
	} else if (mf.verbose) {
		mf_print_maps(stderr);
	}

	mf_build();
	mf.target = mf.n;
	mf.pass = 0;
	mf_validate();
	mf_check_warnings();
	for (mf.pass = 1; !passes || mf.pass <= passes; mf.pass++) {
		mf.seq = 0;
		if (mf.pass > mf.promote && mf.top < full) {
			mf.top = full;
			if (mf.verbose)
				fprintf(stderr, "pass %u: top lifted to %llx\n",
					mf.pass, (unsigned long long)mf.top);
		}
		mf_pass();
	}
	printf("maple-fuzz: %u passes: height %u-%u, %zu-%zu ranges\n",
	       mf.pass - 1, mf.hmin, mf.hmax, mf.nmin, mf.nmax);

	mtree_destroy(&mf.mt);
	rcu_barrier();
	if (mt_nr_allocated())
		mf_fail("%u nodes leaked", mt_nr_allocated());
	mf_check_warnings();
	for (i = 0; i < mf.nvmas; i++)
		free(mf.vmas[i]);
	mf.nvmas = 0;
	mf.n = 0;
}

int main(int argc, char **argv)
{
	int opt;
	unsigned int i;

	mf.top_arg = ((u64)1 << 47) - 1;
	mf.passes = 100;
	mf.ops = 1000;
	mf.flags = MT_FLAGS_ALLOC_RANGE | MT_FLAGS_LOCK_EXTERN | MT_FLAGS_USE_RCU;
	mf.seed = (u64)time(NULL) ^ (u64)getpid();
	mf.crash = "maple-fuzz-crash.txt";

	while ((opt = getopt(argc, argv, "m:g:t:F:s:n:o:pb:P:f:aA:r:RLlvW:c:h")) != -1) {
		switch (opt) {
		case 'm':
			mf.maps = optarg;
			break;
		case 'c':
			mf.crash = optarg;
			break;
		case 'g':
			mf.gen = strtoull(optarg, NULL, 0);
			break;
		case 't':
			mf.top_arg = strtoull(optarg, NULL, 0);
			break;
		case 'F':
			mf.floor_arg = strtoull(optarg, NULL, 0);
			break;
		case 'P':
			mf.promote = strtoul(optarg, NULL, 0);
			break;
		case 's':
			mf.seed = strtoull(optarg, NULL, 0);
			break;
		case 'n':
			mf.passes = strtoul(optarg, NULL, 0);
			break;
		case 'o':
			mf.ops = strtoul(optarg, NULL, 0);
			break;
		case 'p':
			mf.pfn = true;
			break;
		case 'b':
			mf.below4g = strtoul(optarg, NULL, 0);
			break;
		case 'f':
			if (!strcmp(optarg, "plain"))
				mf.flags &= ~MT_FLAGS_ALLOC_RANGE;
			else if (!strcmp(optarg, "marks"))
				mf.flags = (mf.flags & ~MT_FLAGS_ALLOC_RANGE) |
					   MT_FLAGS_MARKS;
			else if (strcmp(optarg, "alloc"))
				mf_usage();
			break;
		case 'a':
			mf.sweep = true;
			break;
		case 'A':
			mf.configs = strtoul(optarg, NULL, 0);
			break;
		case 'r':
			mf.nreaders = strtoul(optarg, NULL, 0);
			break;
		case 'R':
			mf.flags &= ~MT_FLAGS_USE_RCU;
			break;
		case 'L':
			mf.flags &= ~MT_FLAGS_LOCK_EXTERN;
			break;
		case 'l':
			mf.leak = true;
			break;
		case 'v':
			mf.verbose = true;
			break;
		case 'W':
			mf.save = optarg;
			break;
		default:
			mf_usage();
		}
	}
	if (mf.maps && mf.gen)
		mf_usage();
	if (!mf.maps && !mf.gen)
		mf.gen = 1000;
	if (mf.nreaders && !(mf.flags & MT_FLAGS_USE_RCU))
		mf_usage();
	if (mf.below4g && mf.floor_arg > U32_MAX)
		mf_usage();

	mf.rng = mf.seed ? mf.seed : 1;
	printf("maple-fuzz: seed %llu\n", (unsigned long long)mf.seed);

	signal(SIGABRT, mf_sigabrt);
#ifdef __SANITIZE_ADDRESS__
	{
		extern void __sanitizer_set_death_callback(void (*)(void));

		__sanitizer_set_death_callback(mf_sanitizer_death);
	}
#endif

	rcu_register_thread();
	maple_tree_init();
	mf_readers = calloc(mf.nreaders, sizeof(*mf_readers));
	for (i = 0; i < mf.nreaders; i++)
		mf_readers[i].rng = mf.rng ^ (0x9E3779B97F4A7C15ULL * (i + 1));

	if (mf.sweep) {
		unsigned int passes = mf.passes ? mf.passes : 100, c = 0, n = 0;
		unsigned int lock = mf.flags & MT_FLAGS_LOCK_EXTERN;
		unsigned int nreaders = mf.nreaders;
		bool rcu = true;

		for (;;) {
			printf("maple-fuzz: %s tree%s\n", mf_config[c].name,
			       rcu ? "" : ", no rcu");
			/* Readers need RCU; without them reset and the toggle run. */
			mf.nreaders = rcu ? nreaders : 0;
			mf_run(mf_config[c].flags | lock |
			       (rcu ? MT_FLAGS_USE_RCU : 0), mf_config[c].pfn,
			       passes);
			/* A replay stops after the configuration that failed. */
			if (++n == mf.configs)
				break;
			if (++c == ARRAY_SIZE(mf_config)) {
				c = 0;
				rcu = !rcu;
				if (rcu && mf.passes)
					break;
			}
		}
	} else {
		mf_run(mf.flags, mf.pfn, mf.passes);
	}

	free(mf_readers);
	free(mf.vmas);
	free(mf.v);
	rcu_unregister_thread();
	printf("maple-fuzz: %u passes of %u ops, seed %llu: ok\n", mf.passes,
	       mf.ops, (unsigned long long)mf.seed);
	return 0;
}
