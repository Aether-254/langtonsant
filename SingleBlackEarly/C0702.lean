import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0702 : checkSingleBlackFast (22, -7) 7575 .west (-11, 4) (-19, -17) = true := by
  decide +kernel

end LangtonsAnt
