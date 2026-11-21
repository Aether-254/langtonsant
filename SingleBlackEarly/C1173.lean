import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1173 : checkSingleBlackFast (29, -19) 11088 .north (-3, 1) (-27, 3) = true := by
  decide +kernel

end LangtonsAnt
