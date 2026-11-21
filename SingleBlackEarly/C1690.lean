import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1690 : checkSingleBlackFast (-45, -20) 20127 .east (25, 4) (-21, -43) = true := by
  decide +kernel

end LangtonsAnt
