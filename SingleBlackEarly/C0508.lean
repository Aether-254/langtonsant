import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0508 : checkSingleBlackFast (-7, 1) 8448 .south (-11, -11) (-23, -17) = true := by
  decide +kernel

end LangtonsAnt
