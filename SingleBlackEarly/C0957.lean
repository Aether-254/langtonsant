import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0957 : checkSingleBlackFast2 (6, 17) 15643 .east (-6, -6) (-19, -26) = true := by
  decide +kernel

end LangtonsAnt
