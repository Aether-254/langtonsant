import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1723 : checkSingleBlackFast (-46, -27) 20192 .north (25, 21) (-51, -13) = true := by
  decide +kernel

end LangtonsAnt
