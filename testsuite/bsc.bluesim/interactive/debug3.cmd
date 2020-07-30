while {true} {
  if [catch {sim nextedge}] {break}
  puts "---- [sim time] ----"
}
