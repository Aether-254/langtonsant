import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0563 : checkSingleBlackFast (18, -5) 4452 .south (-12, -3) (-18, 1) = true := by
  decide +kernel

end LangtonsAnt
