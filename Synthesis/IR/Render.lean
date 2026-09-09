import Synthesis.IR.Query

namespace Synthesis.IR
set_option autoImplicit false

/-- Length-delimited segments avoid ambiguous punctuation in names. Not a serializer. -/
def renderId (id : QualifiedId) : String :=
  String.intercalate "/" (id.segments.map fun s => s!"{s.utf8ByteSize}:{s}")

def renderContract (id : ContractId) : String := s!"{renderId id.name}@{id.version}"

def EntityRef.render (r : EntityRef) : String :=
  let base := r.definition.map renderId |>.getD "module"
  let instances := r.instances.map fun s => s!"/instance({s.text.utf8ByteSize}:{s.text})"
  base ++ String.join instances ++ String.join (r.steps.map fun step =>
    match step with
    | .parameter n => s!"/parameter({n.text})"
    | .port n => s!"/port({n.text})"
    | .instance n => s!"/instance-declaration({n.text})"
    | .junction n => s!"/junction({n.text})"
    | .operation n => s!"/operation({n.text})"
    | .result n => s!"/result({n.text})"
    | .argument n => s!"/argument[{n}]"
    | .attribute c n => s!"/attribute({renderContract c})[{n}]"
    | .binding n => s!"/binding({n.text})")

def Diagnostic.render (d : Diagnostic) : String :=
  let severity := match d.severity with
    | .error => "error" | .warning => "warning" | .note => "note"
  s!"{severity} {renderContract d.code}: {d.message}" ++
    (d.subject.map (fun r => "\n  at " ++ r.render) |>.getD "") ++
    (d.source.map (fun span => s!"\n  source: {span.source}:{span.start}..{span.stop}") |>.getD "") ++
    String.join (d.related.map (fun r => "\n  related: " ++ r.render)) ++
    (d.expected.map (fun value => "\n  expected: " ++ reprStr value) |>.getD "") ++
    (d.actual.map (fun value => "\n  actual: " ++ reprStr value) |>.getD "") ++
    String.join (d.notes.map ("\n  note: " ++ ·)) ++
    (d.remediation.map ("\n  hint: " ++ ·) |>.getD "")

/-- Functional inspection is available without command elaboration or text parsing. -/
def Module.renderSummary (m : Module) : String :=
  s!"IR schema {m.schema}; root {renderId m.root}; " ++
    s!"{m.foldDefinitions 0 (fun n _ => n + 1)} definitions; {m.walk.length} entities"

end Synthesis.IR
