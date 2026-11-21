import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0049 : checkSingleBlackFast (2, -4) 1792 .south (-7, -1) (-11, -5) = true := by
  decide +kernel

end LangtonsAnt
