import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0277 : checkSingleBlackFast (16, 9) 3351 .west (-12, -4) (-11, -14) = true := by
  decide +kernel

end LangtonsAnt
