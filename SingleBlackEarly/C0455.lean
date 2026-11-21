import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0455 : checkSingleBlackFast (19, 9) 8104 .south (-20, -15) (-28, -17) = true := by
  decide +kernel

end LangtonsAnt
