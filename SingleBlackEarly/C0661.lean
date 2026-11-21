import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0661 : checkSingleBlackFast (13, -10) 12783 .east (-7, -3) (-18, -23) = true := by
  decide +kernel

end LangtonsAnt
