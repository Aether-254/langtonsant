import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1149 : checkSingleBlackFast (17, -19) 10468 .north (-1, 1) (-25, 3) = true := by
  decide +kernel

end LangtonsAnt
