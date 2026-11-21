import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0264 : checkSingleBlackFast (10, 10) 9104 .north (-2, -3) (-24, -7) = true := by
  decide +kernel

end LangtonsAnt
