import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1930 : checkSingleBlackFast2 (-69, -42) 19250 .north (26, 19) (-53, -32) = true := by
  decide +kernel

end LangtonsAnt
