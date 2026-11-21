import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2025 : checkSingleBlackFast (-76, -54) 19755 .east (28, 22) (-5, -40) = true := by
  decide +kernel

end LangtonsAnt
