import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1913 : checkSingleBlackFast (-66, -43) 14679 .west (20, 30) (-49, 10) = true := by
  decide +kernel

end LangtonsAnt
