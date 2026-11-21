import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1355 : checkSingleBlackFast (-17, 7) 31940 .north (10, -11) (-46, 13) = true := by
  decide +kernel

end LangtonsAnt
