import Synthesis.Design.Model

namespace Synthesis.Design
set_option autoImplicit false
universe u

/-- Typed attributes have exact decoders. Their meaning remains owned by the contract;
codec correctness does not establish physical validity. -/
structure AttributeCodec (Value : Type u) where
  contract : ContractId
  encode : Value → IR.Data
  decode : IR.Data → Option Value
  exact : ∀ value, decode (encode value) = some value

def AttributeCodec.pack {Value : Type u} (codec : AttributeCodec Value) (value : Value) : IR.Attribute :=
  ⟨codec.contract, codec.encode value⟩

def AttributeCodec.unpack {Value : Type u} (codec : AttributeCodec Value) (attr : IR.Attribute) :
    Option Value :=
  if attr.contract == codec.contract then codec.decode attr.value else none

@[simp] theorem AttributeCodec.unpack_pack {Value : Type u} (codec : AttributeCodec Value)
    (value : Value) : codec.unpack (codec.pack value) = some value := by
  simp [unpack, pack, codec.exact]

/-- Literal construction shares the domain's exact typed encoding. Extension acceptance
is a separate check; an encoding alone does not prove a typing rule. -/
def Encoding.literal {Value : Type u} (encoding : Encoding Value) (value : Value) : IR.Term :=
  .literal encoding.type (encoding.encode value)

/-- Parameterized type families reuse an exact payload codec. A single payload
argument avoids forcing the core to know a domain's shape or scalar vocabulary. -/
structure TypeFamily (Shape : Type u) where
  payload : AttributeCodec Shape

def TypeFamily.type {Shape : Type u} (family : TypeFamily Shape) (shape : Shape) : IR.TypeExpr :=
  ⟨family.payload.contract, [family.payload.encode shape]⟩

def TypeFamily.decode {Shape : Type u} (family : TypeFamily Shape) (type : IR.TypeExpr) : Option Shape :=
  if type.constructor == family.payload.contract then
    match type.arguments with
    | [value] => family.payload.decode value
    | _ => none
  else none

@[simp] theorem TypeFamily.decode_type {Shape : Type u} (family : TypeFamily Shape)
    (shape : Shape) : family.decode (family.type shape) = some shape := by
  simp [decode, type, family.payload.exact]

/-- A fixed signature is a common case, not the universal operation ontology.
Dependent/value-dependent signatures remain ordinary Extension callbacks. -/
structure OperationSchema where
  contract : ContractId
  inputs : List IR.TypeExpr
  output : IR.TypeExpr

def OperationSchema.signature (schema : OperationSchema) (id : ContractId)
    (arguments : List IR.Term) (types : List IR.TypeExpr) : Option IR.TypeExpr :=
  if id == schema.contract && types == schema.inputs && arguments.length == types.length then
    some schema.output else none

/-- Explicit interface construction keeps connector meaning separate from value type.
Roles and junction laws remain extension contracts. -/
structure InterfaceSchema where
  contract : ContractId
  valueType : IR.TypeExpr
  role : ContractId

def InterfaceSchema.port (schema : InterfaceSchema) (name : Symbol) : IR.Port :=
  ⟨name, schema.contract, schema.valueType, schema.role, []⟩

end Synthesis.Design
