import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0156 : checkSingleBlackFast2 (0, 7) 18399 .west (1, 11) (-32, -5) = true := by
  decide +kernel

end LangtonsAnt
