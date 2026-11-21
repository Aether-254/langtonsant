import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1971 : checkSingleBlackFast (-72, -45) 13136 .north (24, 16) (-50, -32) = true := by
  decide +kernel

end LangtonsAnt
