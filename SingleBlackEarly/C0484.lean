import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0484 : checkSingleBlackFast (7, 15) 6981 .west (-4, 2) (-22, -9) = true := by
  decide +kernel

end LangtonsAnt
