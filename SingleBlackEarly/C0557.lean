import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0557 : checkSingleBlackFast (18, -6) 21024 .south (-7, 0) (-23, -26) = true := by
  decide +kernel

end LangtonsAnt
