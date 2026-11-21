import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1899 : checkSingleBlackFast (-62, -43) 21024 .north (33, 29) (-59, -21) = true := by
  decide +kernel

end LangtonsAnt
