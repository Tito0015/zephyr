/**
 * SPDX-License-Identifier: Apache-2.0
 * SPDX-FileCopyrightText: Copyright (c) 2026 Tarek Tarek
 *
 * Veraptos VaaS — Zephyr mutex leak heuristic (structural)
* @kind problem
 * @id veraptos/zephyr-mutex-unlock-on-error
 * @name Zephyr mutex may leak on error goto
* @problem.severity warning
 * @tags security external/veraptos zephyr rtos
 */

import cpp

predicate hasErrorGoto(Function f) {
exists(GotoStmt g | g.getEnclosingFunction() = f)
}

from Function f
where
exists(FunctionCall lock |
lock.getEnclosingFunction() = f and lock.getTarget().getName() = "k_mutex_lock"
) and
  hasErrorGoto(f) and
  not exists(FunctionCall unlock |
unlock.getEnclosingFunction() = f and unlock.getTarget().getName() = "k_mutex_unlock"
)
select f, "Function locks mutex but has error goto without k_mutex_unlock."
