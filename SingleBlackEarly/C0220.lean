import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0220 : checkSingleBlackFast (9, 8) 2426 .south (-7, -6) (-12, -7) = true := by
  decide +kernel

end LangtonsAnt
