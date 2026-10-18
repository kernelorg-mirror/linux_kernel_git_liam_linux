// SPDX-License-Identifier: GPL-2.0-or-later

/* Very simple shim around the maple tree. */

#include "maple-shared.h"
#include <linux/slab.h>

/* Nodes are kfree()d; send them back through the cache so the counts hold. */
#define kfree(p)	kmem_cache_free(maple_node_cache, p)
#include "../../../lib/maple_tree.c"
#undef kfree

void maple_rcu_cb(struct rcu_head *head) {
	struct maple_node *node = container_of(head, struct maple_node, rcu);

	kmem_cache_free(maple_node_cache, node);
}
