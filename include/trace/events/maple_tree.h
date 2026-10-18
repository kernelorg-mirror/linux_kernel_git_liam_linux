/* SPDX-License-Identifier: GPL-2.0 */
#undef TRACE_SYSTEM
#define TRACE_SYSTEM maple_tree

#if !defined(_TRACE_MM_H) || defined(TRACE_HEADER_MULTI_READ)
#define _TRACE_MM_H


#include <linux/tracepoint.h>

struct ma_state;

TRACE_EVENT(ma_op,

	TP_PROTO(const char *fn, struct ma_state *mas),

	TP_ARGS(fn, mas),

	TP_STRUCT__entry(
			__field(const char *, fn)
			__field(u64, min)
			__field(u64, max)
			__field(u64, index)
			__field(u64, last)
			__field(void *, node)
	),

	TP_fast_assign(
			__entry->fn		= fn;
			__entry->min		= mas->min;
			__entry->max		= mas->max;
			__entry->index		= mas->index;
			__entry->last		= mas->last;
			__entry->node		= mas->node;
	),

	TP_printk("%s\tNode: %p (%llu %llu) range: %llu-%llu",
		  __entry->fn,
		  (void *) __entry->node,
		  (unsigned long long) __entry->min,
		  (unsigned long long) __entry->max,
		  (unsigned long long) __entry->index,
		  (unsigned long long) __entry->last
	)
)
TRACE_EVENT(ma_read,

	TP_PROTO(const char *fn, struct ma_state *mas),

	TP_ARGS(fn, mas),

	TP_STRUCT__entry(
			__field(const char *, fn)
			__field(u64, min)
			__field(u64, max)
			__field(u64, index)
			__field(u64, last)
			__field(void *, node)
	),

	TP_fast_assign(
			__entry->fn		= fn;
			__entry->min		= mas->min;
			__entry->max		= mas->max;
			__entry->index		= mas->index;
			__entry->last		= mas->last;
			__entry->node		= mas->node;
	),

	TP_printk("%s\tNode: %p (%llu %llu) range: %llu-%llu",
		  __entry->fn,
		  (void *) __entry->node,
		  (unsigned long long) __entry->min,
		  (unsigned long long) __entry->max,
		  (unsigned long long) __entry->index,
		  (unsigned long long) __entry->last
	)
)

TRACE_EVENT(ma_write,

	TP_PROTO(const char *fn, struct ma_state *mas, u64 piv,
		 void *val),

	TP_ARGS(fn, mas, piv, val),

	TP_STRUCT__entry(
			__field(const char *, fn)
			__field(u64, min)
			__field(u64, max)
			__field(u64, index)
			__field(u64, last)
			__field(u64, piv)
			__field(void *, val)
			__field(void *, node)
	),

	TP_fast_assign(
			__entry->fn		= fn;
			__entry->min		= mas->min;
			__entry->max		= mas->max;
			__entry->index		= mas->index;
			__entry->last		= mas->last;
			__entry->piv		= piv;
			__entry->val		= val;
			__entry->node		= mas->node;
	),

	TP_printk("%s\tNode %p (%llu %llu) range:%llu-%llu piv (%llu) val %p",
		  __entry->fn,
		  (void *) __entry->node,
		  (unsigned long long) __entry->min,
		  (unsigned long long) __entry->max,
		  (unsigned long long) __entry->index,
		  (unsigned long long) __entry->last,
		  (unsigned long long) __entry->piv,
		  (void *) __entry->val
	)
)
#endif /* _TRACE_MM_H */

/* This part must be outside protection */
#include <trace/define_trace.h>
