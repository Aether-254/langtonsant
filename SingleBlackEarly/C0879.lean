import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0879 : checkSingleBlackFast2 (-9, 0) 17073 .west (-11, 2) (-30, -24) = true := by
  decide +kernel

end LangtonsAnt
