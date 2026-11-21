import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0763 : checkSingleBlackFast (16, -14) 11219 .west (-9, 2) (-25, -17) = true := by
  decide +kernel

end LangtonsAnt
