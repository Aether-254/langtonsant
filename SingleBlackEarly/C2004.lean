import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2004 : checkSingleBlackFast (-75, -52) 20373 .east (35, 20) (12, -54) = true := by
  decide +kernel

end LangtonsAnt
