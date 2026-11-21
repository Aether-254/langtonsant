import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1546 : checkSingleBlackFast (-32, -11) 24640 .north (2, 8) (-6, -34) = true := by
  decide +kernel

end LangtonsAnt
