import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1968 : checkSingleBlackFast2 (-68, -48) 16444 .north (29, 19) (-55, -35) = true := by
  decide +kernel

end LangtonsAnt
