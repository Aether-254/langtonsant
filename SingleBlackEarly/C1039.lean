import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1039 : checkSingleBlackFast (-13, 2) 31799 .east (-7, 1) (-30, -29) = true := by
  decide +kernel

end LangtonsAnt
