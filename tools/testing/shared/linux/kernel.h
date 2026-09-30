/* SPDX-License-Identifier: GPL-2.0 */
#ifndef _KERNEL_H
#define _KERNEL_H

#include "../../include/linux/kernel.h"
#include <string.h>
#include <stdio.h>
#include <limits.h>

#include <linux/compiler.h>
#include <linux/err.h>
#include <linux/bitops.h>
#include <linux/log2.h>
#include "../../../include/linux/kconfig.h"
#include <linux/types.h>

#ifndef U32_MAX
#define U32_MAX		((u32)~0U)
#endif
#ifndef U64_MAX
#define U64_MAX		((u64)~0ULL)
#endif

#define printk printf
#define pr_err printk
#define pr_info printk
#define pr_debug printk
#define pr_cont printk
#define schedule()
#define PAGE_SHIFT	12

#define EXPORT_PER_CPU_SYMBOL_GPL(x)
#endif /* _KERNEL_H */
