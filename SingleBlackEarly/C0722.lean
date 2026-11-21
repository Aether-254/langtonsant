import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0722 : checkSingleBlackFast (7, -12) 8898 .south (-8, -2) (-21, -9) = true := by
  decide +kernel

end LangtonsAnt
