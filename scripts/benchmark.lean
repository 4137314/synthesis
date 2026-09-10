import Tests.Scale

/-- Optional scale runner; times are observations, never semantic assertions. -/
def main (args : List String) : IO Unit := do
  let output ← IO.getStdout
  let count := args.head?.bind String.toNat? |>.getD 10000
  let start ← IO.monoMsNow
  let m := Tests.Scale.model count
  let index := m.buildIndex
  IO.println s!"index_probe={(index.findDefinition (Tests.Scale.id_ 0)).isSome}"
  output.flush
  let built ← IO.monoMsNow
  let mut hits := 0
  for n in List.range count do
    if (index.findDefinition (Tests.Scale.id_ n)).isSome then hits := hits + 1
  IO.println s!"lookup_hits={hits}"
  output.flush
  let looked ← IO.monoMsNow
  let walked := m.walk.length
  IO.println s!"walk_entities={walked}"
  output.flush
  let traversed ← IO.monoMsNow
  let encoded := m.encode
  IO.println s!"encoded_bytes={encoded.utf8ByteSize}"
  output.flush
  let written ← IO.monoMsNow
  let decoded := Synthesis.IR.Module.decode encoded (256 * 1024 * 1024)
  IO.println s!"decode_ok={decoded.isOk}"
  output.flush
  let read ← IO.monoMsNow
  IO.println s!"definitions={count} hits={hits} entities={walked} bytes={encoded.utf8ByteSize} decoded={decoded.isOk}"
  output.flush
  IO.println s!"build_ms={built-start} lookup_ms={looked-built} walk_ms={traversed-looked} encode_ms={written-traversed} decode_ms={read-written}"
  output.flush
