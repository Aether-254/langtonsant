import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1011 : checkSingleBlackFast (-12, 6) 10067 .east (-2, -2) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
