import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0301 : checkSingleBlackFast (8, 13) 5008 .south (-14, -10) (-20, -12) = true := by
  decide +kernel

end LangtonsAnt
