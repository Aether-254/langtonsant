import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1903 : checkSingleBlackFast (-61, -43) 12632 .north (20, 12) (-46, -28) = true := by
  decide +kernel

end LangtonsAnt
