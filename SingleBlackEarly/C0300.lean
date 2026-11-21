import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0300 : checkSingleBlackFast (7, 13) 2951 .east (-7, -10) (-13, -7) = true := by
  decide +kernel

end LangtonsAnt
