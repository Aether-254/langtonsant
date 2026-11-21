import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0939 : checkSingleBlackFast (-7, 14) 9043 .east (1, -6) (-21, -21) = true := by
  decide +kernel

end LangtonsAnt
