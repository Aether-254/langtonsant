import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2000 : checkSingleBlackFast2 (-73, -51) 16521 .west (24, 33) (-53, 13) = true := by
  decide +kernel

end LangtonsAnt
