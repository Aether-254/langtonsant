import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1900 : checkSingleBlackFast (-62, -44) 28667 .east (34, 22) (-7, -44) = true := by
  decide +kernel

end LangtonsAnt
