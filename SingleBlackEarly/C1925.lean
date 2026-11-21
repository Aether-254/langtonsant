import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1925 : checkSingleBlackFast (-63, -45) 12736 .north (21, 13) (-47, -29) = true := by
  decide +kernel

end LangtonsAnt
