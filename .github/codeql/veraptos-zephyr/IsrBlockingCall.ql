/**
 * SPDX-License-Identifier: Apache-2.0
 * SPDX-FileCopyrightText: Copyright (c) 2026 Tarek Tarek
 *
 * Veraptos VaaS — Zephyr ISR blocking call (structural, intra-procedural)
* @kind problem
 * @id veraptos/zephyr-isr-blocking-call
 * @name Zephyr ISR must not call blocking APIs with K_FOREVER
* @problem.severity error
 * @tags security external/veraptos zephyr rtos
 */

import cpp

predicate blockingSink(string name) {
    name = "k_sem_take" or
    name = "k_mutex_lock" or
    name = "k_sleep" or
    name = "k_msgq_get" or
    name = "k_condvar_wait" or
    name = "k_queue_get"
}

predicate isIsrLike(Function f) {
  f.getName().regexpMatch(".*_isr$")
  or exists(MacroInvocation mi |
    mi.getEnclosingFunction() = f and
    mi.getMacroName().matches("%ISR_DIRECT_DECLARE%")
  )
}

from FunctionCall call, Function f
where
  call.getEnclosingFunction() = f and
  isIsrLike(f) and
  blockingSink(call.getTarget().getName()) and
  exists(Expr arg |
    arg = call.getAnArgument() and
    arg.toString().matches("%K_FOREVER%")
  )
select call, "ISR-like function must not invoke blocking API with K_FOREVER."
