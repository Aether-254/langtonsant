import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0694 : checkSingleBlackFast (21, -11) 23195 .east (-5, 0) (-21, -21) = true := by
  decide +kernel

end LangtonsAnt
