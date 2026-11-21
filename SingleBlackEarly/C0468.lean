import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0468 : checkSingleBlackFast (16, 12) 29582 .south (-3, -5) (-30, -4) = true := by
  decide +kernel

end LangtonsAnt
