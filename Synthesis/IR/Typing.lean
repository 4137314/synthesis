import Synthesis.IR.Extension

namespace Synthesis.IR
set_option autoImplicit false

mutual
  /-- Propositional typing rules, independently presented from the inference procedure. -/
  inductive Typed (ext : Extension) (context : Context) : Term → TypeExpr → Prop where
    | literal (ty : TypeExpr) (value : Data) (id : ty.constructor.valid = true)
        (supported : ext.type ty = true) (literal : ext.literal ty value = true) :
        Typed ext context (.literal ty value) ty
    | variable (name : Symbol) (ty : TypeExpr)
        (found : (context.find? (·.1 == name)).map (·.2) = some ty) :
        Typed ext context (.variable name) ty
    | application (op : ContractId) (args : List Term) (types : List TypeExpr) (ty : TypeExpr)
        (id : op.valid = true) (arguments : ArgumentsTyped ext context args types)
        (signature : ext.application op args types = some ty)
        (resultId : ty.constructor.valid = true) (supported : ext.type ty = true) :
        Typed ext context (.apply op args) ty

  inductive ArgumentsTyped (ext : Extension) (context : Context) : List Term → List TypeExpr → Prop where
    | nil : ArgumentsTyped ext context [] []
    | cons {term : Term} {ty : TypeExpr} {terms : List Term} {types : List TypeExpr}
        (head : Typed ext context term ty) (tail : ArgumentsTyped ext context terms types) :
        ArgumentsTyped ext context (term :: terms) (ty :: types)
end

mutual
  theorem Extension.infer_sound (ext : Extension) (context : Context) (term : Term) (ty : TypeExpr)
      (h : ext.infer context term = some ty) : Typed ext context term ty := by
    cases term with
    | literal declared value =>
      simp only [Extension.infer] at h
      split at h
      · rename_i accepted
        cases h
        simp only [Bool.and_eq_true] at accepted
        exact .literal _ _ accepted.1.1 accepted.1.2 accepted.2
      · cases h
    | «variable» name => exact .variable name ty h
    | «apply» op args =>
      cases hi : op.valid with
      | false => simp [Extension.infer, hi] at h
      | true =>
        cases ha : ext.inferList context args with
        | none => simp [Extension.infer, hi, ha] at h
        | some types =>
          cases hs : ext.application op args types with
          | none => simp [Extension.infer, hi, ha, hs] at h
          | some result =>
            simp only [Extension.infer, hi, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte, bind, Option.bind, ha, hs] at h
            split at h
            · rename_i accepted
              cases h
              simp only [Bool.and_eq_true] at accepted
              exact .application op args types _ hi (ext.inferList_sound context args types ha)
                hs accepted.1 accepted.2
            · cases h
  termination_by structural term

  theorem Extension.inferList_sound (ext : Extension) (context : Context)
      (terms : List Term) (types : List TypeExpr) (h : ext.inferList context terms = some types) :
      ArgumentsTyped ext context terms types := by
    cases terms with
    | nil => cases h; exact .nil
    | cons term rest =>
      cases ht : ext.infer context term with
      | none => simp [Extension.inferList, ht] at h
      | some ty =>
        cases hr : ext.inferList context rest with
        | none => simp [Extension.inferList, ht, hr] at h
        | some tail =>
          simp [Extension.inferList, ht, hr] at h
          subst types
          exact .cons (ext.infer_sound context term ty ht) (ext.inferList_sound context rest tail hr)
  termination_by structural terms
end

end Synthesis.IR
