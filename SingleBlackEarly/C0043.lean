import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0043 : checkSingleBlackFast (-3, 1) 3871 .west (-3, 5) (-12, -9) = true := by
  decide +kernel

end LangtonsAnt
