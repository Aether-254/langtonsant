import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0123 : checkSingleBlackFast (6, 7) 1848 .south (-7, -4) (-11, 0) = true := by
  decide +kernel

end LangtonsAnt
