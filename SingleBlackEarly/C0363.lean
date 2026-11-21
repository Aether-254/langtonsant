import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0363 : checkSingleBlackFast (14, 1) 5096 .south (-10, -6) (-18, -12) = true := by
  decide +kernel

end LangtonsAnt
