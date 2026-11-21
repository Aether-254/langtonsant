import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0209 : checkSingleBlackFast (9, 6) 7572 .south (-12, -17) (-18, -17) = true := by
  decide +kernel

end LangtonsAnt
