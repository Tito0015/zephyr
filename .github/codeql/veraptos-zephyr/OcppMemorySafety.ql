/**
 * SPDX-License-Identifier: Apache-2.0
 * SPDX-FileCopyrightText: Copyright (c) 2026 Tarek Tarek
 *
 * Veraptos VaaS — Zephyr OCPP session lifetime and CISTR string bounds (structural)
 * @kind problem
 * @id veraptos/zephyr-ocpp-memory-safety
 * @name Zephyr OCPP unterminated CISTR strncpy or session k_free without is_busy guard
 * @problem.severity error
 * @tags security external/veraptos zephyr rtos ocpp
 */

import cpp

/** OCPP case-insensitive string capacity macro: CISTR20, CISTR50, ... */
predicate bareCistrMacro(Expr n) { n.toString().regexpMatch("^CISTR[0-9]+$") }

predicate inOcppTree(Function f) {
  f.getFile().getRelativePath().matches("%ocpp%")
}

predicate isStrncpy(FunctionCall call) {
  exists(Function target |
    call.getTarget() = target and
  (target.hasName("strncpy") or target.hasGlobalName("strncpy"))
  )
}

predicate functionHasExplicitNulStore(Function f) {
  exists(AssignExpr assign |
    assign.getEnclosingFunction() = f and
    assign.getRValue().toString().regexpMatch(".*\\\\0.*")
  )
}

predicate unterminatedBareCistrStrncpy(FunctionCall call) {
  isStrncpy(call) and
  inOcppTree(call.getEnclosingFunction()) and
  exists(Expr n |
    n = call.getArgument(2) and
    bareCistrMacro(n)
  ) and
  not functionHasExplicitNulStore(call.getEnclosingFunction())
}

predicate callsOcppMeterValues(Function f) {
  exists(FunctionCall mc |
    mc.getEnclosingFunction() = f and
    mc.getTarget().hasName("ocpp_meter_values")
  )
}

predicate functionTouchesIsBusyField(Function f) {
  exists(Expr e |
    e.getEnclosingFunction() = f and
    e.toString().matches("%is_busy%")
  )
}

predicate sessionFreeWithoutBusyGuard(FunctionCall freeCall) {
  freeCall.getTarget().hasName("k_free") and
  inOcppTree(freeCall.getEnclosingFunction()) and
  (
    freeCall.getEnclosingFunction().hasName("ocpp_session_close") or
    callsOcppMeterValues(freeCall.getEnclosingFunction())
  ) and
  not functionTouchesIsBusyField(freeCall.getEnclosingFunction())
}

from FunctionCall call, string msg
where
  (
    unterminatedBareCistrStrncpy(call) and
    msg =
      "strncpy uses bare CISTR macro with no explicit NUL store in this function (OCPP network string)."
  )
  or
  (
    sessionFreeWithoutBusyGuard(call) and
    msg = "k_free in OCPP session path without is_busy / is_closing lifetime guard."
  )
select call, msg