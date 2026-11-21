import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0753 : checkSingleBlackFast2 (24, -11) 15436 .north (-4, 1) (-28, 3) = true := by
  decide +kernel

end LangtonsAnt
