/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Curve25519Dalek.Funs
public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Curve25519Dalek.backend

/-- `get_selected_backend`: always the serial backend (no SIMD backend is translated). -/
@[step]
theorem get_selected_backend_spec :
    get_selected_backend ⦃ (r : BackendKind) => r = BackendKind.Serial ⦄ := by
  unfold get_selected_backend
  simp only [WP.spec_ok]

end Curve25519Dalek.backend
