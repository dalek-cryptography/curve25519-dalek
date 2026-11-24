module
public import ForHumans.Specs.External.Subtle.Contract
@[expose] public section
set_option linter.style.whitespace false
set_option linter.unusedVariables false
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Curve25519Dalek

/-- `subtle.Choice.unwrap_u8` meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.unwrap_u8_spec
    (c : subtle.Choice) (hc : c.IsValid) :
    subtle.Choice.unwrap_u8 c ⦃ r => r = c ⦄ :=
  RustAx.subtle.unwrap_u8 c hc

/-- `Bool.Insts.CoreConvertFromChoice.from` meets its contract (`RustAx.subtle`). -/
@[step]
theorem Bool.Insts.CoreConvertFromChoice.from_spec
    (c : subtle.Choice)
    (hc : c.IsValid) :
    Bool.Insts.CoreConvertFromChoice.from c ⦃ b => b = (c != 0#u8) ⦄ :=
  RustAx.subtle.bool_from_choice c hc

/-- `subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand_spec
    (a b : subtle.Choice)
    (ha : a.IsValid) (hb : b.IsValid) :
    subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand a b ⦃ c =>
      c.IsValid ∧ c = a &&& b ⦄ :=
  RustAx.subtle.choice_bitand a b ha hb

/-- `subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor_spec
    (a b : subtle.Choice)
    (ha : a.IsValid) (hb : b.IsValid) :
    subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor a b ⦃ c =>
      c.IsValid ∧ c = a ||| b ⦄ :=
  RustAx.subtle.choice_bitor a b ha hb

/-- `subtle.Choice.Insts.CoreOpsBitNotChoice.not` meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.Insts.CoreOpsBitNotChoice.not_spec
    (c : subtle.Choice) (hc : c.IsValid) :
    subtle.Choice.Insts.CoreOpsBitNotChoice.not c ⦃ r => r.IsValid ∧ r = 1#u8 &&& ~~~c ⦄ :=
  RustAx.subtle.choice_not c hc

/-- `subtle.Choice.Insts.CoreConvertFromU8.from` meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.Choice.Insts.CoreConvertFromU8.from_spec
    (input : Std.U8)
    (h : input = 0#u8 ∨ input = 1#u8) :
    subtle.Choice.Insts.CoreConvertFromU8.from input ⦃ c => c.IsValid ∧ c = input ⦄ :=
  RustAx.subtle.choice_from_u8 input h

/-- `Slice.Insts.SubtleConstantTimeEq.ct_eq` meets its contract (`RustAx.subtle`). -/
@[step]
theorem Slice.Insts.SubtleConstantTimeEq.ct_eq_spec
    {T : Type}
    (inst : subtle.ConstantTimeEq T)
    (hinst : ∀ x y, inst.ct_eq x y ⦃ c => (x = y → c = 1#u8) ∧ (x ≠ y → c = 0#u8) ⦄)
    (a b : Slice T) :
    Slice.Insts.SubtleConstantTimeEq.ct_eq inst a b ⦃ c =>
      c.IsValid ∧ (a = b → c = 1#u8) ∧ (a ≠ b → c = 0#u8) ⦄ :=
  RustAx.subtle.slice_ct_eq inst hinst a b

/-- `U8.Insts.SubtleConstantTimeEq.ct_eq` meets its contract (`RustAx.subtle`). -/
@[step]
theorem U8.Insts.SubtleConstantTimeEq.ct_eq_spec
    (a b : Std.U8) :
    U8.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
      c.IsValid ∧ c = if a = b then 1#u8 else 0#u8 ⦄ :=
  RustAx.subtle.u8_ct_eq a b

/-- `U16.Insts.SubtleConstantTimeEq.ct_eq` meets its contract (`RustAx.subtle`). -/
@[step]
theorem U16.Insts.SubtleConstantTimeEq.ct_eq_spec
    (a b : Std.U16) :
    U16.Insts.SubtleConstantTimeEq.ct_eq a b ⦃ c =>
      c.IsValid ∧ c = if a = b then 1#u8 else 0#u8 ⦄ :=
  RustAx.subtle.u16_ct_eq a b

/-- `U8.Insts.SubtleConditionallySelectable.conditional_select`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U8.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U8) (choice : subtle.Choice) (hc : choice.IsValid) :
    U8.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u8_conditional_select a b choice hc

/-- `U8.Insts.SubtleConditionallySelectable.conditional_assign`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U8.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U8) (choice : subtle.Choice) (hc : choice.IsValid) :
    U8.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u8_conditional_assign a b choice hc

/-- `U32.Insts.SubtleConditionallySelectable.conditional_select`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid) :
    U32.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u32_conditional_select a b choice hc

/-- `U32.Insts.SubtleConditionallySelectable.conditional_assign`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid) :
    U32.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u32_conditional_assign a b choice hc

/-- `U32.Insts.SubtleConditionallySelectable.conditional_swap`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U32.Insts.SubtleConditionallySelectable.conditional_swap_spec
    (a b : Std.U32) (choice : subtle.Choice) (hc : choice.IsValid) :
    U32.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃ r =>
      (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄ :=
  RustAx.subtle.u32_conditional_swap a b choice hc

/-- `U64.Insts.SubtleConditionallySelectable.conditional_select`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_select_spec
    (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid) :
    U64.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u64_conditional_select a b choice hc

/-- `U64.Insts.SubtleConditionallySelectable.conditional_assign`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_assign_spec
    (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid) :
    U64.Insts.SubtleConditionallySelectable.conditional_assign a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.u64_conditional_assign a b choice hc

/-- `U64.Insts.SubtleConditionallySelectable.conditional_swap`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem U64.Insts.SubtleConditionallySelectable.conditional_swap_spec
    (a b : Std.U64) (choice : subtle.Choice) (hc : choice.IsValid) :
    U64.Insts.SubtleConditionallySelectable.conditional_swap a b choice ⦃ r =>
      (choice = 0#u8 → r = (a, b)) ∧ (choice = 1#u8 → r = (b, a)) ⦄ :=
  RustAx.subtle.u64_conditional_swap a b choice hc

/-- `Array.Insts.SubtleConditionallySelectable.conditional_select`
meets its contract (`RustAx.subtle`). -/
@[step]
theorem Array.Insts.SubtleConditionallySelectable.conditional_select_spec
    {T : Type} {N : Std.Usize} (inst : subtle.ConditionallySelectable T)
    (a b : Array T N) (choice : subtle.Choice) (hc : choice.IsValid)
    (hinst : ∀ x y, inst.conditional_assign x y choice ⦃ r =>
      (choice = 0#u8 → r = x) ∧ (choice = 1#u8 → r = y) ⦄) :
    Array.Insts.SubtleConditionallySelectable.conditional_select inst a b choice ⦃ r =>
      (choice = 0#u8 → r = a) ∧ (choice = 1#u8 → r = b) ⦄ :=
  RustAx.subtle.array_conditional_select inst a b choice hc hinst

/-- `subtle.CtOption.new` meets its contract (`RustAx.subtle`). -/
@[step]
theorem subtle.CtOption.new_spec
    {T : Type} (value : T) (is_some : subtle.Choice)
    (his_some : is_some.IsValid) :
    subtle.CtOption.new value is_some ⦃ opt => opt = { value, is_some } ⦄ :=
  RustAx.subtle.ctOption_new value is_some his_some
