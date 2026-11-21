import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0952 : checkSingleBlackFast (6, 16) 8528 .north (-1, -3) (-23, 1) = true := by
  decide +kernel

end LangtonsAnt
