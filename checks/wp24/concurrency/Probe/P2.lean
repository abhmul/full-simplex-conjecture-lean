import Init

#eval show IO Unit from do
  let start ← IO.monoMsNow
  IO.sleep 500
  let stop ← IO.monoMsNow
  IO.println s!"FSC_CONCURRENCY 2 {start} {stop}"
