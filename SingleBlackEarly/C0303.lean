import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0303 : checkSingleBlackFast (6, 11) 3743 .east (-5, -6) (-7, -13) = true := by
  decide +kernel

end LangtonsAnt
