import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0675 : checkSingleBlackFast (15, -12) 9588 .north (-11, 7) (-11, -19) = true := by
  decide +kernel

end LangtonsAnt
